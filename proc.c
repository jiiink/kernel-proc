#include <stddef.h>
#include <signal.h>
#include <assert.h>
#include <string.h>

#include "vm.h"
#include "clock.h"
#include "spinlock.h"
#include "arch_proto.h"

#include <minix/syslib.h>

static void idle(void);
static int mini_receive(struct proc *caller_ptr, endpoint_t src,
	message *m_buff_usr, int flags);
static int mini_senda(struct proc *caller_ptr, asynmsg_t *table, size_t
	size);
static int deadlock(int function, register struct proc *caller,
	endpoint_t src_dst_e);
static int try_async(struct proc *caller_ptr);
static int try_one(endpoint_t receive_e, struct proc *src_ptr,
	struct proc *dst_ptr);
static struct proc * pick_proc(void);
static void enqueue_head(struct proc *rp);

static struct priv idle_priv;

static void set_idle_name(char * name, int n)
{
        const int MAX_VALUE = 999;
        const char IDLE_PREFIX[] = "idle";
        const int PREFIX_LENGTH = 4;
        
        if (n > MAX_VALUE) 
                n = MAX_VALUE;

        for (int i = 0; i < PREFIX_LENGTH; i++) {
                name[i] = IDLE_PREFIX[i];
        }

        int i = PREFIX_LENGTH;
        int divisor = 100;
        int started_output = 0;

        while (divisor > 0) {
                int digit = n / divisor;
                n %= divisor;

                if (started_output || digit != 0 || divisor == 1) {
                        started_output = 1;
                        name[i++] = '0' + digit;
                }
                
                divisor /= 10;
        }

        name[i] = '\0';
}

#define PICK_ANY	1
#define PICK_HIGHERONLY	2

#define BuildNotifyMessage(m_ptr, src, dst_ptr) \
	memset((m_ptr), 0, sizeof(*(m_ptr)));				\
	(m_ptr)->m_type = NOTIFY_MESSAGE;				\
	(m_ptr)->m_notify.timestamp = get_monotonic();		\
	switch (src) {							\
	case HARDWARE:							\
		(m_ptr)->m_notify.interrupts =			\
			priv(dst_ptr)->s_int_pending;			\
		priv(dst_ptr)->s_int_pending = 0;			\
		break;							\
	case SYSTEM:							\
		memcpy(&(m_ptr)->m_notify.sigset,			\
			&priv(dst_ptr)->s_sig_pending,			\
			sizeof(sigset_t));				\
		sigemptyset(&priv(dst_ptr)->s_sig_pending);		\
		break;							\
	}

static message m_notify_buff = { 0, NOTIFY_MESSAGE };

void init_process_entry(struct proc *rp, int index)
{
    rp->p_rts_flags = RTS_SLOT_FREE;
    rp->p_magic = PMAGIC;
    rp->p_nr = index;
    rp->p_endpoint = _ENDPOINT(0, rp->p_nr);
    rp->p_scheduler = NULL;
    rp->p_priority = 0;
    rp->p_quantum_size_ms = 0;
    arch_proc_reset(rp);
}

void init_privilege_entry(struct priv *sp, int index)
{
    sp->s_proc_nr = NONE;
    sp->s_id = (sys_id_t) index;
    ppriv_addr[index] = sp;
    sp->s_sig_mgr = NONE;
    sp->s_bak_sig_mgr = NONE;
}

void init_idle_process(int cpu_index)
{
    struct proc *ip = get_cpu_var_ptr(cpu_index, idle_proc);
    ip->p_endpoint = IDLE;
    ip->p_priv = &idle_priv;
    ip->p_rts_flags |= RTS_PROC_STOP;
    set_idle_name(ip->p_name, cpu_index);
}

void init_process_table(void)
{
    struct proc *rp;
    int i;
    
    for (rp = BEG_PROC_ADDR, i = -NR_TASKS; rp < END_PROC_ADDR; ++rp, ++i) {
        init_process_entry(rp, i);
    }
}

void init_privilege_table(void)
{
    struct priv *sp;
    int i;
    
    for (sp = BEG_PRIV_ADDR, i = 0; sp < END_PRIV_ADDR; ++sp, ++i) {
        init_privilege_entry(sp, i);
    }
}

void init_idle_processes(void)
{
    int i;
    
    idle_priv.s_flags = IDL_F;
    for (i = 0; i < CONFIG_MAX_CPUS; i++) {
        init_idle_process(i);
    }
}

void proc_init(void)
{
    init_process_table();
    init_privilege_table();
    init_idle_processes();
}

static void switch_address_space_idle(void)
{
#ifdef CONFIG_SMP
	switch_address_space(proc_addr(VM_PROC_NR));
#endif
}

static void setup_idle_process(void)
{
    struct proc *p = get_cpulocal_var_ptr(idle_proc);
    get_cpulocal_var(proc_ptr) = p;
    
    if (priv(p)->s_flags & BILLABLE)
        get_cpulocal_var(bill_ptr) = p;
}

static void handle_idle_timer(void)
{
#ifdef CONFIG_SMP
    get_cpulocal_var(cpu_is_idle) = 1;
    if (cpuid != bsp_cpu_id)
        stop_local_timer();
    else
        restart_local_timer();
#else
    restart_local_timer();
#endif
}

static void wait_for_idle_interrupt(void)
{
    volatile int *v = get_cpulocal_var_ptr(idle_interrupted);
    interrupts_enable();
    while (!*v)
        arch_pause();
    interrupts_disable();
    *v = 0;
}

static void perform_idle_halt(void)
{
#if !SPROFILE
    halt_cpu();
#else
    if (!sprofiling)
        halt_cpu();
    else
        wait_for_idle_interrupt();
#endif
}

static void idle(void)
{
    setup_idle_process();
    switch_address_space_idle();
    handle_idle_timer();
    context_stop(proc_addr(KERNEL));
    perform_idle_halt();
}

void vm_suspend(struct proc *caller, const struct proc *target,
        const vir_bytes linaddr, const vir_bytes len, const int type,
        const int writeflag)
{
        assert(!RTS_ISSET(caller, RTS_VMREQUEST));
        assert(!RTS_ISSET(target, RTS_VMREQUEST));

        RTS_SET(caller, RTS_VMREQUEST);

        caller->p_vmrequest.req_type = VMPTYPE_CHECK;
        caller->p_vmrequest.target = target->p_endpoint;
        caller->p_vmrequest.params.check.start = linaddr;
        caller->p_vmrequest.params.check.length = len;
        caller->p_vmrequest.params.check.writeflag = writeflag;
        caller->p_vmrequest.type = type;

        caller->p_vmrequest.nextrequestor = vmrequest;
        
        if (!vmrequest) {
                if (OK != send_sig(VM_PROC_NR, SIGKMEM)) {
                        panic("send_sig failed");
                }
        }
        
        vmrequest = caller;
}

static void handle_copy_failure(struct proc *rp)
{
    if (rp->p_misc_flags & MF_MSGFAILED) {
        printf("WARNING wrong user pointer 0x%08lx from "
               "process %s / %d\n",
               rp->p_delivermsg_vir,
               rp->p_name,
               rp->p_endpoint);
        cause_sig(rp->p_nr, SIGSEGV);
        return;
    }
    
    vm_suspend(rp, rp, rp->p_delivermsg_vir,
              sizeof(message), VMSTYPE_DELIVERMSG, 1);
    rp->p_misc_flags |= MF_MSGFAILED;
}

static void handle_copy_success(struct proc *rp)
{
    rp->p_delivermsg.m_source = NONE;
    rp->p_misc_flags &= ~(MF_DELIVERMSG | MF_MSGFAILED);
    
    if (!(rp->p_misc_flags & MF_CONTEXT_SET)) {
        rp->p_reg.retreg = OK;
    }
}

static void delivermsg(struct proc *rp)
{
    assert(!RTS_ISSET(rp, RTS_VMREQUEST));
    assert(rp->p_misc_flags & MF_DELIVERMSG);
    assert(rp->p_delivermsg.m_source != NONE);
    
    if (copy_msg_to_user(&rp->p_delivermsg,
                        (message *) rp->p_delivermsg_vir)) {
        handle_copy_failure(rp);
        return;
    }
    
    handle_copy_success(rp);
}

static void handle_kernel_call_resume(struct proc *p)
{
    kernel_call_resume(p);
}

static void handle_deliver_message(struct proc *p)
{
    TRACE(VF_SCHEDULING, printf("delivering to %s / %d\n",
        p->p_name, p->p_endpoint););
    delivermsg(p);
}

static void handle_syscall_defer(struct proc *p)
{
    assert (!(p->p_misc_flags & MF_SC_ACTIVE));
    arch_do_syscall(p);
    if ((p->p_misc_flags & MF_SIG_DELAY) &&
            !RTS_ISSET(p, RTS_SENDING))
        sig_delay_done(p);
}

static void handle_syscall_trace(struct proc *p)
{
    p->p_misc_flags &= ~(MF_SC_TRACE | MF_SC_ACTIVE);
    cause_sig(proc_nr(p), SIGTRAP);
}

static void clear_syscall_active(struct proc *p)
{
    p->p_misc_flags &= ~MF_SC_ACTIVE;
}

static int has_syscall_trace_and_active(struct proc *p)
{
    return (p->p_misc_flags & MF_SC_TRACE) && 
           (p->p_misc_flags & MF_SC_ACTIVE);
}

static void handle_misc_flags(struct proc *p)
{
    if (p->p_misc_flags & MF_KCALL_RESUME) {
        handle_kernel_call_resume(p);
        return;
    }
    
    if (p->p_misc_flags & MF_DELIVERMSG) {
        handle_deliver_message(p);
        return;
    }
    
    if (p->p_misc_flags & MF_SC_DEFER) {
        handle_syscall_defer(p);
        return;
    }
    
    if (has_syscall_trace_and_active(p)) {
        handle_syscall_trace(p);
        return;
    }
    
    if (p->p_misc_flags & MF_SC_ACTIVE) {
        clear_syscall_active(p);
    }
}

void switch_to_user(void)
{
	struct proc * p;
#ifdef CONFIG_SMP
	int tlb_must_refresh = 0;
#endif

	p = get_cpulocal_var(proc_ptr);
	if (proc_is_runnable(p))
		goto check_misc_flags;

not_runnable_pick_new:
	handle_preempted_process(p);
	p = wait_for_runnable_process();
	get_cpulocal_var(proc_ptr) = p;

#ifdef CONFIG_SMP
	tlb_must_refresh = should_refresh_tlb(p);
#endif
	switch_address_space(p);

check_misc_flags:
	assert(p);
	assert(proc_is_runnable(p));
	
	if (!process_misc_flags(p))
		goto not_runnable_pick_new;

	if (!p->p_cpu_time_left)
		proc_no_time(p);

	if (!proc_is_runnable(p))
		goto not_runnable_pick_new;

	log_process_start(p);
	p = arch_finish_switch_to_user();
	assert(p->p_cpu_time_left);

	context_stop(proc_addr(KERNEL));
	setup_fpu_state(p);
	p->p_misc_flags &= ~MF_CONTEXT_SET;
	validate_process_segments(p);
	
#ifdef CONFIG_SMP
	handle_tlb_flush(p, tlb_must_refresh);
#endif
	
	restart_local_timer();
	restore_user_context(p);
	NOT_REACHABLE;
}

static void handle_preempted_process(struct proc *p)
{
	if (!proc_is_preempted(p))
		return;
		
	p->p_rts_flags &= ~RTS_PREEMPTED;
	if (!proc_is_runnable(p))
		return;
		
	if (p->p_cpu_time_left)
		enqueue_head(p);
	else
		enqueue(p);
}

static struct proc* wait_for_runnable_process(void)
{
	struct proc *p;
	while (!(p = pick_proc())) {
		idle();
	}
	return p;
}

#ifdef CONFIG_SMP
static int should_refresh_tlb(struct proc *p)
{
	return (p->p_misc_flags & MF_FLUSH_TLB) && (get_cpulocal_var(ptproc) == p);
}

static void handle_tlb_flush(struct proc *p, int tlb_must_refresh)
{
	if (!(p->p_misc_flags & MF_FLUSH_TLB))
		return;
		
	if (tlb_must_refresh)
		refresh_tlb();
	p->p_misc_flags &= ~MF_FLUSH_TLB;
}
#endif

static int process_misc_flags(struct proc *p)
{
#define MISC_FLAGS_TO_HANDLE (MF_KCALL_RESUME | MF_DELIVERMSG | \
                             MF_SC_DEFER | MF_SC_TRACE | MF_SC_ACTIVE)

	while (p->p_misc_flags & MISC_FLAGS_TO_HANDLE) {
		assert(proc_is_runnable(p));
		handle_misc_flags(p);
		if (!proc_is_runnable(p))
			return 0;
	}
	return 1;
}

static void setup_fpu_state(struct proc *p)
{
	if (get_cpulocal_var(fpu_owner) != p)
		enable_fpu_exception();
	else
		disable_fpu_exception();
}

static void validate_process_segments(struct proc *p)
{
#if defined(__i386__)
	assert(p->p_seg.p_cr3 != 0);
#elif defined(__arm__)
	assert(p->p_seg.p_ttbr != 0);
#endif
}

static void log_process_start(struct proc *p)
{
	TRACE(VF_SCHEDULING, printf("cpu %d starting %s / %d "
				"pc 0x%08x\n",
		cpuid, p->p_name, p->p_endpoint, p->p_reg.pc););
#if DEBUG_TRACE
	p->p_schedules++;
#endif
}

static void print_ipc_warning(const char *message, const char *callname, 
                             struct proc *caller_ptr, endpoint_t src_dst_e)
{
#if DEBUG_ENABLE_IPC_WARNINGS
    if (callname) {
        printf(message, callname, proc_nr(caller_ptr), src_dst_e);
    } else {
        printf(message, proc_nr(caller_ptr), src_dst_e);
    }
#endif
}

static int validate_call_number(int call_nr, struct proc *caller_ptr, 
                               endpoint_t src_dst_e, char **callname)
{
    const int MAX_CALL_NR = 31;
    
    if (call_nr < 0 || call_nr > IPCNO_HIGHEST || call_nr > MAX_CALL_NR) {
        print_ipc_warning("sys_call: trap %d not allowed, caller %d, src_dst %d\n", 
                         NULL, caller_ptr, src_dst_e);
        return ETRAPDENIED;
    }
    
    *callname = ipc_call_names[call_nr];
    if (!*callname) {
        print_ipc_warning("sys_call: trap %d not allowed, caller %d, src_dst %d\n", 
                         NULL, caller_ptr, src_dst_e);
        return ETRAPDENIED;
    }
    
    return OK;
}

static int validate_endpoint(int call_nr, endpoint_t src_dst_e, int *src_dst_p)
{
    if (src_dst_e == ANY) {
        if (call_nr != RECEIVE) {
            return EINVAL;
        }
        *src_dst_p = (int) src_dst_e;
        return OK;
    }
    
    if (!isokendpt(src_dst_e, src_dst_p)) {
        return EDEADSRCDST;
    }
    
    return OK;
}

static int check_send_permission(int call_nr, struct proc *caller_ptr, 
                                int src_dst_p, endpoint_t src_dst_e, 
                                char *callname)
{
    if (call_nr == RECEIVE) {
        return OK;
    }
    
    if (!may_send_to(caller_ptr, src_dst_p)) {
        print_ipc_warning("sys_call: ipc mask denied %s from %d to %d\n",
                         callname, caller_ptr, src_dst_e);
        return ECALLDENIED;
    }
    
    return OK;
}

static int check_trap_permission(struct proc *caller_ptr, int call_nr, 
                                char *callname, int src_dst_p)
{
    if (!(priv(caller_ptr)->s_trap_mask & (1 << call_nr))) {
        print_ipc_warning("sys_call: %s not allowed, caller %d, src_dst %d\n",
                         callname, caller_ptr, src_dst_p);
        return ETRAPDENIED;
    }
    
    return OK;
}

static int check_kernel_destination(int call_nr, int src_dst_p, 
                                   char *callname, struct proc *caller_ptr,
                                   endpoint_t src_dst_e)
{
    if (call_nr == SENDREC || call_nr == RECEIVE) {
        return OK;
    }
    
    if (iskerneln(src_dst_p)) {
        print_ipc_warning("sys_call: trap %s not allowed, caller %d, src_dst %d\n",
                         callname, caller_ptr, src_dst_e);
        return ETRAPDENIED;
    }
    
    return OK;
}

static int validate_ipc_call(struct proc *caller_ptr, int call_nr,
                            endpoint_t src_dst_e, int *src_dst_p)
{
    char *callname;
    int result;
    
    result = validate_call_number(call_nr, caller_ptr, src_dst_e, &callname);
    if (result != OK) {
        return result;
    }
    
    result = validate_endpoint(call_nr, src_dst_e, src_dst_p);
    if (result != OK) {
        return result;
    }
    
    if (src_dst_e != ANY) {
        result = check_send_permission(call_nr, caller_ptr, *src_dst_p, 
                                      src_dst_e, callname);
        if (result != OK) {
            return result;
        }
    }
    
    result = check_trap_permission(caller_ptr, call_nr, callname, *src_dst_p);
    if (result != OK) {
        return result;
    }
    
    result = check_kernel_destination(call_nr, *src_dst_p, callname, 
                                     caller_ptr, src_dst_e);
    if (result != OK) {
        return result;
    }
    
    return OK;
}

static int handle_sendrec(struct proc * caller_ptr, endpoint_t src_dst_e, message *m_ptr)
{
    caller_ptr->p_misc_flags |= MF_REPLY_PEND;
    int result = mini_send(caller_ptr, src_dst_e, m_ptr, 0);
    if (result != OK)
        return result;
    return mini_receive(caller_ptr, src_dst_e, m_ptr, 0);
}

static int handle_receive(struct proc * caller_ptr, endpoint_t src_dst_e, message *m_ptr)
{
    caller_ptr->p_misc_flags &= ~MF_REPLY_PEND;
    IPC_STATUS_CLEAR(caller_ptr);
    return mini_receive(caller_ptr, src_dst_e, m_ptr, 0);
}

static int handle_send(struct proc * caller_ptr, endpoint_t src_dst_e, message *m_ptr)
{
    return mini_send(caller_ptr, src_dst_e, m_ptr, 0);
}

static int handle_notify(struct proc * caller_ptr, endpoint_t src_dst_e)
{
    return mini_notify(caller_ptr, src_dst_e);
}

static int handle_sendnb(struct proc * caller_ptr, endpoint_t src_dst_e, message *m_ptr)
{
    return mini_send(caller_ptr, src_dst_e, m_ptr, NON_BLOCKING);
}

static int do_sync_ipc(struct proc * caller_ptr, int call_nr,
			endpoint_t src_dst_e, message *m_ptr)
{
	int result;
	int src_dst_p;

	assert(call_nr != SENDA);

	result = validate_ipc_call(caller_ptr, call_nr, src_dst_e, &src_dst_p);
	if (result != OK)
		return result;

	switch(call_nr) {
	case SENDREC:
		return handle_sendrec(caller_ptr, src_dst_e, m_ptr);
	case RECEIVE:			
		return handle_receive(caller_ptr, src_dst_e, m_ptr);
	case SEND:			
		return handle_send(caller_ptr, src_dst_e, m_ptr);
	case NOTIFY:
		return handle_notify(caller_ptr, src_dst_e);
	case SENDNB:
		return handle_sendnb(caller_ptr, src_dst_e, m_ptr);
	default:
		return EBADCALL;
	}
}

static int is_trace_without_defer(struct proc *caller_ptr)
{
    return (caller_ptr->p_misc_flags & (MF_SC_TRACE | MF_SC_DEFER)) == MF_SC_TRACE;
}

static void setup_syscall_defer(struct proc *caller_ptr, reg_t r1, reg_t r2, reg_t r3)
{
    caller_ptr->p_misc_flags &= ~MF_SC_TRACE;
    assert(!(caller_ptr->p_misc_flags & MF_SC_DEFER));
    caller_ptr->p_misc_flags |= MF_SC_DEFER;
    
    caller_ptr->p_defer.r1 = r1;
    caller_ptr->p_defer.r2 = r2;
    caller_ptr->p_defer.r3 = r3;
}

static void activate_syscall(struct proc *caller_ptr)
{
    caller_ptr->p_misc_flags &= ~MF_SC_DEFER;
    assert(!(caller_ptr->p_misc_flags & MF_SC_ACTIVE));
    caller_ptr->p_misc_flags |= MF_SC_ACTIVE;
}

static void handle_syscall_trace(struct proc *caller_ptr, reg_t r1, reg_t r2, reg_t r3)
{
    if (is_trace_without_defer(caller_ptr)) {
        setup_syscall_defer(caller_ptr, r1, r2, r3);
        cause_sig(proc_nr(caller_ptr), SIGTRAP);
    } else {
        activate_syscall(caller_ptr);
    }
}

int do_ipc(reg_t r1, reg_t r2, reg_t r3)
{
	struct proc *const caller_ptr = get_cpulocal_var(proc_ptr);
	int call_nr = (int) r1;

	assert(!RTS_ISSET(caller_ptr, RTS_SLOT_FREE));

	kbill_ipc = caller_ptr;

	if (caller_ptr->p_misc_flags & (MF_SC_TRACE | MF_SC_DEFER)) {
		int prev_result = caller_ptr->p_reg.retreg;
		handle_syscall_trace(caller_ptr, r1, r2, r3);
		if (caller_ptr->p_misc_flags & MF_SC_DEFER)
			return prev_result;
	}

	if(caller_ptr->p_misc_flags & MF_DELIVERMSG) {
		panic("sys_call: MF_DELIVERMSG on for %s / %d\n",
			caller_ptr->p_name, caller_ptr->p_endpoint);
	}

	return handle_ipc_call(caller_ptr, call_nr, r2, r3);
}

static int handle_ipc_call(struct proc *caller_ptr, int call_nr, reg_t r2, reg_t r3)
{
	switch(call_nr) {
	case SENDREC:
	case SEND:			
	case RECEIVE:			
	case NOTIFY:
	case SENDNB:
		return handle_sync_ipc(caller_ptr, call_nr, r2, r3);
	case SENDA:
		return handle_async_ipc(caller_ptr, r2, r3);
	case MINIX_KERNINFO:
		return handle_kerninfo(caller_ptr);
	default:
		return EBADCALL;
	}
}

static int handle_sync_ipc(struct proc *caller_ptr, int call_nr, reg_t r2, reg_t r3)
{
	caller_ptr->p_accounting.ipc_sync++;
	return do_sync_ipc(caller_ptr, call_nr, (endpoint_t) r2, (message *) r3);
}

#define MAX_ASYNC_MSG_SIZE (16 * (NR_TASKS + NR_PROCS))

static int handle_async_ipc(struct proc *caller_ptr, reg_t r2, reg_t r3)
{
	size_t msg_size = (size_t) r2;
	
	caller_ptr->p_accounting.ipc_async++;
	
	if (msg_size > MAX_ASYNC_MSG_SIZE)
		return EDOM;
		
	return mini_senda(caller_ptr, (asynmsg_t *) r3, msg_size);
}

static int handle_kerninfo(struct proc *caller_ptr)
{
	if(!minix_kerninfo_user)
		return EBADCALL;
		
	arch_set_secondary_ipc_return(caller_ptr, minix_kerninfo_user);
	return OK;
}

static int get_blocked_endpoint(struct proc *xp)
{
    return P_BLOCKEDON(xp);
}

static struct proc* get_validated_proc(endpoint_t endpoint)
{
    int slot;
    struct proc *xp;
    
    okendpt(endpoint, &slot);
    xp = proc_addr(slot);
    assert(proc_ptr_ok(xp));
    assert(!RTS_ISSET(xp, RTS_SLOT_FREE));
    
    return xp;
}

static int check_for_cycle(endpoint_t current_endpoint, endpoint_t target_endpoint)
{
    return (current_endpoint == target_endpoint) ? 1 : 0;
}

static int check_deadlock_cycle(struct proc *cp, endpoint_t src_dst_e)
{
    int group_size = 1;
    
    while (src_dst_e != ANY) {
        struct proc *xp = get_validated_proc(src_dst_e);
        group_size++;
        
        src_dst_e = get_blocked_endpoint(xp);
        
        if (src_dst_e == NONE) {
            return 0;
        }
        
        if (check_for_cycle(src_dst_e, cp->p_endpoint)) {
            return group_size;
        }
    }
    
    return 0;
}

static int is_bidirectional_block(struct proc *xp, int function)
{
    return (xp->p_rts_flags ^ (function << 2)) & RTS_SENDING;
}

static struct proc *get_process_from_endpoint(endpoint_t endpoint, int *slot)
{
    okendpt(endpoint, slot);
    return proc_addr(*slot);
}

#if DEBUG_ENABLE_IPC_WARNINGS
static void collect_deadlock_processes(struct proc *cp, endpoint_t src_dst_e, 
                                       struct proc *processes[], int group_size)
{
    int i = 0;
    int src_dst_slot;
    
    processes[i++] = cp;
    
    while (src_dst_e != ANY && i < group_size) {
        struct proc *xp = get_process_from_endpoint(src_dst_e, &src_dst_slot);
        processes[i++] = xp;
        src_dst_e = P_BLOCKEDON(xp);
    }
}

static void print_deadlock_header(struct proc *processes[], int group_size)
{
    printf("deadlock between these processes:\n");
    for(int i = 0; i < group_size; i++) {
        printf(" %10s ", processes[i]->p_name);
    }
    printf("\n\n");
}

static void print_deadlock_details(struct proc *processes[], int group_size)
{
    for(int i = 0; i < group_size; i++) {
        print_proc(processes[i]);
        proc_stacktrace(processes[i]);
    }
}

static void report_deadlock(struct proc *cp, endpoint_t src_dst_e, int group_size)
{
    struct proc *processes[NR_PROCS + NR_TASKS];
    
    collect_deadlock_processes(cp, src_dst_e, processes, group_size);
    print_deadlock_header(processes, group_size);
    print_deadlock_details(processes, group_size);
}
#endif

static int deadlock(int function, register struct proc *cp, endpoint_t src_dst_e)
{
    const int BIDIRECTIONAL_DEADLOCK_SIZE = 2;
    int group_size = check_deadlock_cycle(cp, src_dst_e);

    if (group_size == BIDIRECTIONAL_DEADLOCK_SIZE) {
        int src_dst_slot;
        struct proc *xp = get_process_from_endpoint(src_dst_e, &src_dst_slot);
        if (!is_bidirectional_block(xp, function)) {
            return 0;
        }
    }

#if DEBUG_ENABLE_IPC_WARNINGS
    if (group_size > 0) {
        report_deadlock(cp, src_dst_e, group_size);
    }
#endif
    
    return group_size;
}

static int check_specific_source(sys_map_t *map, int src_id, int asynm)
{
#ifdef CONFIG_SMP
    struct proc *p;
    
    if (!get_sys_bit(*map, src_id))
        return NULL_PRIV_ID;
    
    p = proc_addr(id_to_nr(src_id));
    if (asynm && RTS_ISSET(p, RTS_VMINHIBIT)) {
        p->p_misc_flags |= MF_SENDA_VM_MISS;
        return NULL_PRIV_ID;
    }
    return src_id;
#else
    if (get_sys_bit(*map, src_id))
        return src_id;
    return NULL_PRIV_ID;
#endif
}

static int find_first_set_bit(sys_map_t *map, int start_id)
{
    int src_id = start_id;
    while (src_id < NR_SYS_PROCS && !get_sys_bit(*map, src_id))
        src_id++;
    return src_id;
}

#ifdef CONFIG_SMP
static int process_smp_chunk(sys_map_t *map, int start_id, int asynm)
{
    struct proc *p;
    int src_id = start_id;
    
    while (src_id < NR_SYS_PROCS) {
        src_id = find_first_set_bit(map, src_id);
        if (src_id >= NR_SYS_PROCS)
            break;
            
        p = proc_addr(id_to_nr(src_id));
        if (!asynm || !RTS_ISSET(p, RTS_VMINHIBIT))
            return src_id;
            
        p->p_misc_flags |= MF_SENDA_VM_MISS;
        src_id++;
    }
    return NR_SYS_PROCS;
}
#endif

static int search_any_source(sys_map_t *map, int asynm)
{
    int src_id;
    
    for (src_id = 0; src_id < NR_SYS_PROCS; src_id += BITCHUNK_BITS) {
        if (get_sys_bits(*map, src_id) == 0)
            continue;
            
#ifdef CONFIG_SMP
        src_id = process_smp_chunk(map, src_id, asynm);
#else
        src_id = find_first_set_bit(map, src_id);
#endif
        if (src_id < NR_SYS_PROCS)
            return src_id;
    }
    return NULL_PRIV_ID;
}

static int has_pending(sys_map_t *map, int src_p, int asynm)
{
    if (src_p != ANY) {
        int src_id = nr_to_id(src_p);
        return check_specific_source(map, src_id, asynm);
    }
    
    return search_any_source(map, asynm);
}

int has_pending_notify(struct proc * caller, int src_p)
{
	sys_map_t * map = &priv(caller)->s_notify_pending;
	return has_pending(map, src_p, 0);
}

int has_pending_asend(struct proc * caller, int src_p)
{
	sys_map_t * map = &priv(caller)->s_asyn_pending;
	return has_pending(map, src_p, 1);
}

void unset_notify_pending(struct proc * caller, int src_p)
{
	sys_map_t * map = &priv(caller)->s_notify_pending;
	unset_sys_bit(*map, src_p);
}

int mini_send(register struct proc *caller_ptr, endpoint_t dst_e,
	message *m_ptr, const int flags)
{
	register struct proc *dst_ptr;
	int dst_p;
	dst_p = _ENDPOINT_P(dst_e);
	dst_ptr = proc_addr(dst_p);

	if (RTS_ISSET(dst_ptr, RTS_NO_ENDPOINT))
		return EDEADSRCDST;

	if (WILLRECEIVE(caller_ptr->p_endpoint, dst_ptr, (vir_bytes)m_ptr, NULL)) {
		return handle_direct_send(caller_ptr, dst_ptr, m_ptr, flags);
	} else {
		return handle_queued_send(caller_ptr, dst_ptr, dst_e, m_ptr, flags);
	}
}

static int copy_message(struct proc *dst_ptr, message *m_ptr, const int flags)
{
	if (!(flags & FROM_KERNEL)) {
		if(copy_msg_from_user(m_ptr, &dst_ptr->p_delivermsg))
			return EFAULT;
	} else {
		dst_ptr->p_delivermsg = *m_ptr;
		IPC_STATUS_ADD_FLAGS(dst_ptr, IPC_FLG_MSG_FROM_KERNEL);
	}
	return OK;
}

static int copy_message_to_sender(struct proc *caller_ptr, message *m_ptr, const int flags)
{
	if (!(flags & FROM_KERNEL)) {
		if(copy_msg_from_user(m_ptr, &caller_ptr->p_sendmsg))
			return EFAULT;
	} else {
		caller_ptr->p_sendmsg = *m_ptr;
		caller_ptr->p_misc_flags |= MF_SENDING_FROM_KERNEL;
	}
	return OK;
}

static void set_ipc_status(struct proc *caller_ptr, struct proc *dst_ptr, const int flags)
{
	int call = (caller_ptr->p_misc_flags & MF_REPLY_PEND ? SENDREC
		: (flags & NON_BLOCKING ? SENDNB : SEND));
	IPC_STATUS_ADD_CALL(dst_ptr, call);
}

static void queue_sender(struct proc *caller_ptr, struct proc *dst_ptr)
{
	register struct proc **xpp = &dst_ptr->p_caller_q;
	while (*xpp) xpp = &(*xpp)->p_q_link;
	*xpp = caller_ptr;
}

static int handle_direct_send(struct proc *caller_ptr, struct proc *dst_ptr, 
	message *m_ptr, const int flags)
{
	int result;
	assert(!(dst_ptr->p_misc_flags & MF_DELIVERMSG));

	result = copy_message(dst_ptr, m_ptr, flags);
	if (result != OK)
		return result;

	dst_ptr->p_delivermsg.m_source = caller_ptr->p_endpoint;
	dst_ptr->p_misc_flags |= MF_DELIVERMSG;

	set_ipc_status(caller_ptr, dst_ptr, flags);

	if (dst_ptr->p_misc_flags & MF_REPLY_PEND)
		dst_ptr->p_misc_flags &= ~MF_REPLY_PEND;

	RTS_UNSET(dst_ptr, RTS_RECEIVING);

#if DEBUG_IPC_HOOK
	hook_ipc_msgsend(&dst_ptr->p_delivermsg, caller_ptr, dst_ptr);
	hook_ipc_msgrecv(&dst_ptr->p_delivermsg, caller_ptr, dst_ptr);
#endif
	return OK;
}

static int handle_queued_send(struct proc *caller_ptr, struct proc *dst_ptr,
	endpoint_t dst_e, message *m_ptr, const int flags)
{
	int result;
	
	if(flags & NON_BLOCKING)
		return ENOTREADY;

	if (deadlock(SEND, caller_ptr, dst_e))
		return ELOCKED;

	result = copy_message_to_sender(caller_ptr, m_ptr, flags);
	if (result != OK)
		return result;

	RTS_SET(caller_ptr, RTS_SENDING);
	caller_ptr->p_sendto_e = dst_e;

	assert(caller_ptr->p_q_link == NULL);
	queue_sender(caller_ptr, dst_ptr);

#if DEBUG_IPC_HOOK
	hook_ipc_msgsend(&caller_ptr->p_sendmsg, caller_ptr, dst_ptr);
#endif
	return OK;
}

static int has_valid_pending_notification(struct proc *caller_ptr, int src_p)
{
    int src_id = has_pending_notify(caller_ptr, src_p);
    return (src_id != NULL_PRIV_ID) ? src_id : 0;
}

static int get_sender_endpoint(int src_id, endpoint_t *sender_e)
{
    int src_proc_nr = id_to_nr(src_id);
    *sender_e = proc_addr(src_proc_nr)->p_endpoint;
    return src_proc_nr;
}

static int can_receive_from_sender(endpoint_t src_e, endpoint_t sender_e, struct proc *caller_ptr)
{
    return CANRECEIVE(src_e, sender_e, caller_ptr, 0, &m_notify_buff);
}

static void validate_source_process(int src_proc_nr)
{
#if DEBUG_ENABLE_IPC_WARNINGS
    if(src_proc_nr == NONE) {
        printf("mini_receive: sending notify from NONE\n");
    }
#endif
    assert(src_proc_nr != NONE);
}

static void prepare_notification_delivery(struct proc *caller_ptr, int src_proc_nr, endpoint_t sender_e, endpoint_t src_e)
{
    assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));
    assert(src_e == ANY || sender_e == src_e);
    
    BuildNotifyMessage(&caller_ptr->p_delivermsg, src_proc_nr, caller_ptr);
    caller_ptr->p_delivermsg.m_source = sender_e;
    caller_ptr->p_misc_flags |= MF_DELIVERMSG;
    IPC_STATUS_ADD_CALL(caller_ptr, NOTIFY);
}

static int check_pending_notifications(struct proc *caller_ptr, int src_p, endpoint_t src_e)
{
    int src_id = has_valid_pending_notification(caller_ptr, src_p);
    if (!src_id)
        return 0;
    
    endpoint_t sender_e;
    int src_proc_nr = get_sender_endpoint(src_id, &sender_e);
    
    if (!can_receive_from_sender(src_e, sender_e, caller_ptr))
        return 0;
    
    validate_source_process(src_proc_nr);
    unset_notify_pending(caller_ptr, src_id);
    prepare_notification_delivery(caller_ptr, src_proc_nr, sender_e, src_e);
    
    return 1;
}

static int has_pending_async_message(struct proc *caller_ptr, int src_p)
{
    return has_pending_asend(caller_ptr, src_p) != NULL_PRIV_ID;
}

static int try_receive_async_message(endpoint_t src_e, int src_p, struct proc *caller_ptr)
{
    if (src_p != ANY) {
        return try_one(src_e, proc_addr(src_p), caller_ptr);
    }
    return try_async(caller_ptr);
}

static int mark_async_message_received(struct proc *caller_ptr)
{
    IPC_STATUS_ADD_CALL(caller_ptr, SENDA);
    return 1;
}

static int check_async_messages(struct proc *caller_ptr, int src_p, endpoint_t src_e)
{
    if (!has_pending_async_message(caller_ptr, src_p)) {
        return 0;
    }
    
    int r = try_receive_async_message(src_e, src_p, caller_ptr);
    
    if (r == OK) {
        return mark_async_message_received(caller_ptr);
    }
    
    return 0;
}

static int is_valid_sender(struct proc *sender)
{
    assert(!RTS_ISSET(sender, RTS_SLOT_FREE));
    assert(!RTS_ISSET(sender, RTS_NO_ENDPOINT));
    return 1;
}

static void prepare_delivery(struct proc *caller_ptr, struct proc *sender)
{
    assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));
    caller_ptr->p_delivermsg = sender->p_sendmsg;
    caller_ptr->p_delivermsg.m_source = sender->p_endpoint;
    caller_ptr->p_misc_flags |= MF_DELIVERMSG;
}

static void unlink_sender(struct proc **xpp, struct proc *sender)
{
    *xpp = sender->p_q_link;
    sender->p_q_link = NULL;
}

static int check_caller_queue(struct proc *caller_ptr, endpoint_t src_e)
{
    struct proc **xpp = &caller_ptr->p_caller_q;
    
    while (*xpp) {
        struct proc *sender = *xpp;
        endpoint_t sender_e = sender->p_endpoint;
        
        if (CANRECEIVE(src_e, sender_e, caller_ptr, 0, &sender->p_sendmsg)) {
            is_valid_sender(sender);
            prepare_delivery(caller_ptr, sender);
            unlink_sender(xpp, sender);
            return OK;
        }
        xpp = &sender->p_q_link;
    }
    
    return EAGAIN;
}