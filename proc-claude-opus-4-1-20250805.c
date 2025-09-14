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

static void set_idle_name(char *name, int n)
{
    const char prefix[] = "idle";
    const size_t prefix_len = sizeof(prefix) - 1;
    
    if (name == NULL) {
        return;
    }
    
    if (n > 999) {
        n = 999;
    }
    if (n < 0) {
        n = 0;
    }
    
    for (size_t i = 0; i < prefix_len; i++) {
        name[i] = prefix[i];
    }
    
    size_t pos = prefix_len;
    
    if (n >= 100) {
        name[pos++] = '0' + (n / 100);
        n %= 100;
        name[pos++] = '0' + (n / 10);
        name[pos++] = '0' + (n % 10);
    } else if (n >= 10) {
        name[pos++] = '0' + (n / 10);
        name[pos++] = '0' + (n % 10);
    } else {
        name[pos++] = '0' + n;
    }
    
    name[pos] = '\0';
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

void proc_init(void)
{
	struct proc *rp;
	struct priv *sp;
	int i;

	for (rp = BEG_PROC_ADDR, i = -NR_TASKS; rp < END_PROC_ADDR; ++rp, ++i) {
		rp->p_rts_flags = RTS_SLOT_FREE;
		rp->p_magic = PMAGIC;
		rp->p_nr = i;
		rp->p_endpoint = _ENDPOINT(0, rp->p_nr);
		rp->p_scheduler = NULL;
		rp->p_priority = 0;
		rp->p_quantum_size_ms = 0;
		arch_proc_reset(rp);
	}

	for (sp = BEG_PRIV_ADDR, i = 0; sp < END_PRIV_ADDR; ++sp, ++i) {
		sp->s_proc_nr = NONE;
		sp->s_id = (sys_id_t) i;
		ppriv_addr[i] = sp;
		sp->s_sig_mgr = NONE;
		sp->s_bak_sig_mgr = NONE;
	}

	idle_priv.s_flags = IDL_F;
	
	for (i = 0; i < CONFIG_MAX_CPUS; i++) {
		struct proc *ip = get_cpu_var_ptr(i, idle_proc);
		ip->p_endpoint = IDLE;
		ip->p_priv = &idle_priv;
		ip->p_rts_flags |= RTS_PROC_STOP;
		set_idle_name(ip->p_name, i);
	}
}

static void switch_address_space_idle(void)
{
#ifdef CONFIG_SMP
	switch_address_space(proc_addr(VM_PROC_NR));
#endif
}

static void idle(void)
{
	struct proc *p = get_cpulocal_var_ptr(idle_proc);
	get_cpulocal_var(proc_ptr) = p;
	
	if (priv(p)->s_flags & BILLABLE) {
		get_cpulocal_var(bill_ptr) = p;
	}

	switch_address_space_idle();

#ifdef CONFIG_SMP
	get_cpulocal_var(cpu_is_idle) = 1;
	if (cpuid != bsp_cpu_id) {
		stop_local_timer();
	} else {
		restart_local_timer();
	}
#else
	restart_local_timer();
#endif

	context_stop(proc_addr(KERNEL));
	
#if SPROFILE
	if (!sprofiling) {
		halt_cpu();
	} else {
		volatile int *idle_interrupted = get_cpulocal_var_ptr(idle_interrupted);
		interrupts_enable();
		while (!*idle_interrupted) {
			arch_pause();
		}
		interrupts_disable();
		*idle_interrupted = 0;
	}
#else
	halt_cpu();
#endif
}

void vm_suspend(struct proc *caller, const struct proc *target,
        const vir_bytes linaddr, const vir_bytes len, const int type,
        const int writeflag)
{
        if (caller == NULL || target == NULL) {
                panic("vm_suspend: null process pointer");
        }

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
        
        if (vmrequest == NULL) {
                if (send_sig(VM_PROC_NR, SIGKMEM) != OK) {
                        panic("send_sig failed");
                }
        }
        
        vmrequest = caller;
}

static void delivermsg(struct proc *rp)
{
    assert(!RTS_ISSET(rp, RTS_VMREQUEST));
    assert(rp->p_misc_flags & MF_DELIVERMSG);
    assert(rp->p_delivermsg.m_source != NONE);

    if (copy_msg_to_user(&rp->p_delivermsg,
                        (message *) rp->p_delivermsg_vir) == 0) {
        rp->p_delivermsg.m_source = NONE;
        rp->p_misc_flags &= ~(MF_DELIVERMSG | MF_MSGFAILED);

        if (!(rp->p_misc_flags & MF_CONTEXT_SET)) {
            rp->p_reg.retreg = OK;
        }
        return;
    }

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

static void handle_misc_flags(struct proc *p)
{
	if (p == NULL) {
		return;
	}

	if ((p->p_misc_flags & MF_KCALL_RESUME) != 0) {
		kernel_call_resume(p);
		return;
	}

	if ((p->p_misc_flags & MF_DELIVERMSG) != 0) {
		TRACE(VF_SCHEDULING, printf("delivering to %s / %d\n",
			p->p_name, p->p_endpoint););
		delivermsg(p);
		return;
	}

	if ((p->p_misc_flags & MF_SC_DEFER) != 0) {
		assert((p->p_misc_flags & MF_SC_ACTIVE) == 0);
		arch_do_syscall(p);
		if (((p->p_misc_flags & MF_SIG_DELAY) != 0) &&
				!RTS_ISSET(p, RTS_SENDING)) {
			sig_delay_done(p);
		}
		return;
	}

	if (((p->p_misc_flags & MF_SC_TRACE) != 0) && 
	    ((p->p_misc_flags & MF_SC_ACTIVE) != 0)) {
		p->p_misc_flags &= ~(MF_SC_TRACE | MF_SC_ACTIVE);
		cause_sig(proc_nr(p), SIGTRAP);
		return;
	}

	if ((p->p_misc_flags & MF_SC_ACTIVE) != 0) {
		p->p_misc_flags &= ~MF_SC_ACTIVE;
	}
}

void switch_to_user(void)
{
	struct proc *p = get_cpulocal_var(proc_ptr);
	
	if (!proc_is_runnable(p)) {
		p = handle_not_runnable_process(p);
	}
	
	prepare_process_switch(p);
	
	if (!handle_process_misc_flags(p)) {
		p = handle_not_runnable_process(p);
		prepare_process_switch(p);
		handle_process_misc_flags(p);
	}
	
	finalize_process_switch(p);
	restore_user_context(p);
	NOT_REACHABLE;
}

static struct proc* handle_not_runnable_process(struct proc *p)
{
	if (proc_is_preempted(p)) {
		p->p_rts_flags &= ~RTS_PREEMPTED;
		if (proc_is_runnable(p)) {
			if (p->p_cpu_time_left) {
				enqueue_head(p);
			} else {
				enqueue(p);
			}
		}
	}
	
	do {
		p = pick_proc();
		if (!p) {
			idle();
		}
	} while (!p);
	
	get_cpulocal_var(proc_ptr) = p;
	return p;
}

static void prepare_process_switch(struct proc *p)
{
#ifdef CONFIG_SMP
	int tlb_refresh_needed = (p->p_misc_flags & MF_FLUSH_TLB) && 
	                         (get_cpulocal_var(ptproc) == p);
	if (tlb_refresh_needed) {
		get_cpulocal_var(tlb_must_refresh) = 1;
	}
#endif
	switch_address_space(p);
}

static int handle_process_misc_flags(struct proc *p)
{
	assert(p);
	assert(proc_is_runnable(p));
	
	const unsigned int flags_to_handle = MF_KCALL_RESUME | MF_DELIVERMSG |
	                                     MF_SC_DEFER | MF_SC_TRACE | MF_SC_ACTIVE;
	
	while (p->p_misc_flags & flags_to_handle) {
		assert(proc_is_runnable(p));
		handle_misc_flags(p);
		if (!proc_is_runnable(p)) {
			return 0;
		}
	}
	
	if (!p->p_cpu_time_left) {
		proc_no_time(p);
		if (!proc_is_runnable(p)) {
			return 0;
		}
	}
	
	return 1;
}

static void finalize_process_switch(struct proc *p)
{
	TRACE(VF_SCHEDULING, printf("cpu %d starting %s / %d pc 0x%08x\n",
		cpuid, p->p_name, p->p_endpoint, p->p_reg.pc););
	
#if DEBUG_TRACE
	p->p_schedules++;
#endif
	
	p = arch_finish_switch_to_user();
	assert(p->p_cpu_time_left);
	
	context_stop(proc_addr(KERNEL));
	
	if (get_cpulocal_var(fpu_owner) != p) {
		enable_fpu_exception();
	} else {
		disable_fpu_exception();
	}
	
	p->p_misc_flags &= ~MF_CONTEXT_SET;
	
#if defined(__i386__)
	assert(p->p_seg.p_cr3 != 0);
#elif defined(__arm__)
	assert(p->p_seg.p_ttbr != 0);
#endif

#ifdef CONFIG_SMP
	if (p->p_misc_flags & MF_FLUSH_TLB) {
		if (get_cpulocal_var(tlb_must_refresh)) {
			refresh_tlb();
		}
		p->p_misc_flags &= ~MF_FLUSH_TLB;
		get_cpulocal_var(tlb_must_refresh) = 0;
	}
#endif
	
	restart_local_timer();
}

static int validate_ipc_call(struct proc * caller_ptr, int call_nr, 
                              endpoint_t src_dst_e, int *src_dst_p)
{
	const char *callname;

	if (caller_ptr == NULL || src_dst_p == NULL) {
		return EINVAL;
	}

	if (call_nr < 0 || call_nr >= 32 || call_nr > IPCNO_HIGHEST) {
#if DEBUG_ENABLE_IPC_WARNINGS
		printf("sys_call: trap %d not allowed, caller %d, src_dst %d\n", 
		    call_nr, proc_nr(caller_ptr), src_dst_e);
#endif
		return ETRAPDENIED;
	}

	callname = ipc_call_names[call_nr];
	if (callname == NULL) {
#if DEBUG_ENABLE_IPC_WARNINGS
		printf("sys_call: trap %d not allowed, caller %d, src_dst %d\n", 
		    call_nr, proc_nr(caller_ptr), src_dst_e);
#endif
		return ETRAPDENIED;
	}

	if (src_dst_e == ANY) {
		if (call_nr != RECEIVE) {
			return EINVAL;
		}
		*src_dst_p = (int) src_dst_e;
	} else {
		if (!isokendpt(src_dst_e, src_dst_p)) {
			return EDEADSRCDST;
		}

		if (call_nr != RECEIVE && !may_send_to(caller_ptr, *src_dst_p)) {
#if DEBUG_ENABLE_IPC_WARNINGS
			printf("sys_call: ipc mask denied %s from %d to %d\n",
				callname, caller_ptr->p_endpoint, src_dst_e);
#endif
			return ECALLDENIED;
		}
	}

	if ((priv(caller_ptr)->s_trap_mask & (1U << call_nr)) == 0) {
#if DEBUG_ENABLE_IPC_WARNINGS
		printf("sys_call: %s not allowed, caller %d, src_dst %d\n", 
		    callname, proc_nr(caller_ptr), *src_dst_p);
#endif
		return ETRAPDENIED;
	}

	if (call_nr != SENDREC && call_nr != RECEIVE && iskerneln(*src_dst_p)) {
#if DEBUG_ENABLE_IPC_WARNINGS
		printf("sys_call: trap %s not allowed, caller %d, src_dst %d\n",
		     callname, proc_nr(caller_ptr), src_dst_e);
#endif
		return ETRAPDENIED;
	}

	return OK;
}

static int do_sync_ipc(struct proc * caller_ptr, int call_nr,
			endpoint_t src_dst_e, message *m_ptr)
{
	int src_dst_p;
	int result;

	assert(call_nr != SENDA);

	result = validate_ipc_call(caller_ptr, call_nr, src_dst_e, &src_dst_p);
	if (result != OK) {
		return result;
	}

	switch(call_nr) {
	case SEND:
		result = mini_send(caller_ptr, src_dst_e, m_ptr, 0);
		break;
	case RECEIVE:
		caller_ptr->p_misc_flags &= ~MF_REPLY_PEND;
		IPC_STATUS_CLEAR(caller_ptr);
		result = mini_receive(caller_ptr, src_dst_e, m_ptr, 0);
		break;
	case SENDREC:
		caller_ptr->p_misc_flags |= MF_REPLY_PEND;
		result = mini_send(caller_ptr, src_dst_e, m_ptr, 0);
		if (result == OK) {
			result = mini_receive(caller_ptr, src_dst_e, m_ptr, 0);
		}
		break;
	case NOTIFY:
		result = mini_notify(caller_ptr, src_dst_e);
		break;
	case SENDNB:
		result = mini_send(caller_ptr, src_dst_e, m_ptr, NON_BLOCKING);
		break;
	default:
		result = EBADCALL;
		break;
	}

	return result;
}

static void handle_syscall_trace(struct proc *caller_ptr, reg_t r1, reg_t r2, reg_t r3)
{
	if (caller_ptr == NULL) {
		return;
	}

	unsigned int flags = caller_ptr->p_misc_flags;
	unsigned int trace_flags = flags & (MF_SC_TRACE | MF_SC_DEFER);

	if (trace_flags == MF_SC_TRACE) {
		caller_ptr->p_misc_flags = (flags & ~MF_SC_TRACE) | MF_SC_DEFER;
		caller_ptr->p_defer.r1 = r1;
		caller_ptr->p_defer.r2 = r2;
		caller_ptr->p_defer.r3 = r3;
		cause_sig(proc_nr(caller_ptr), SIGTRAP);
		return;
	}

	caller_ptr->p_misc_flags = (flags & ~MF_SC_DEFER) | MF_SC_ACTIVE;
}

int do_ipc(reg_t r1, reg_t r2, reg_t r3)
{
	struct proc *const caller_ptr = get_cpulocal_var(proc_ptr);
	int call_nr = (int) r1;
	int prev_result;

	assert(!RTS_ISSET(caller_ptr, RTS_SLOT_FREE));

	kbill_ipc = caller_ptr;

	if (caller_ptr->p_misc_flags & (MF_SC_TRACE | MF_SC_DEFER)) {
		prev_result = caller_ptr->p_reg.retreg;
		handle_syscall_trace(caller_ptr, r1, r2, r3);
		if (caller_ptr->p_misc_flags & MF_SC_DEFER) {
			return prev_result;
		}
	}

	if (caller_ptr->p_misc_flags & MF_DELIVERMSG) {
		panic("sys_call: MF_DELIVERMSG on for %s / %d\n",
			caller_ptr->p_name, caller_ptr->p_endpoint);
	}

	switch (call_nr) {
	case SENDREC:
	case SEND:
	case RECEIVE:
	case NOTIFY:
	case SENDNB:
		caller_ptr->p_accounting.ipc_sync++;
		return do_sync_ipc(caller_ptr, call_nr, (endpoint_t) r2,
				(message *) r3);
	case SENDA:
		return handle_async_send(caller_ptr, (size_t) r2, (asynmsg_t *) r3);
	case MINIX_KERNINFO:
		return handle_kerninfo_request(caller_ptr);
	default:
		return EBADCALL;
	}
}

static int handle_async_send(struct proc *caller_ptr, size_t msg_size, asynmsg_t *msg)
{
	const size_t MAX_ASYNC_MSG_SIZE = 16 * (NR_TASKS + NR_PROCS);
	
	caller_ptr->p_accounting.ipc_async++;
	
	if (msg_size > MAX_ASYNC_MSG_SIZE) {
		return EDOM;
	}
	
	return mini_senda(caller_ptr, msg, msg_size);
}

static int handle_kerninfo_request(struct proc *caller_ptr)
{
	if (!minix_kerninfo_user) {
		return EBADCALL;
	}
	
	arch_set_secondary_ipc_return(caller_ptr, minix_kerninfo_user);
	return OK;
}

static int check_deadlock_cycle(struct proc *cp, endpoint_t src_dst_e)
{
	struct proc *xp;
	int group_size = 1;
	int src_dst_slot;

	while (src_dst_e != ANY) {
		if (okendpt(src_dst_e, &src_dst_slot) != OK) {
			return 0;
		}
		
		xp = proc_addr(src_dst_slot);
		if (!proc_ptr_ok(xp)) {
			return 0;
		}
		
		if (RTS_ISSET(xp, RTS_SLOT_FREE)) {
			return 0;
		}
		
		group_size++;
		src_dst_e = P_BLOCKEDON(xp);
		
		if (src_dst_e == NONE) {
			return 0;
		}
		
		if (src_dst_e == cp->p_endpoint) {
			return group_size;
		}
	}
	
	return 0;
}

static int deadlock(int function, register struct proc *cp, endpoint_t src_dst_e)
{
	int group_size = check_deadlock_cycle(cp, src_dst_e);

	if (group_size == 2) {
		struct proc *xp;
		int src_dst_slot;
		okendpt(src_dst_e, &src_dst_slot);
		xp = proc_addr(src_dst_slot);
		if ((xp->p_rts_flags ^ (function << 2)) & RTS_SENDING) {
			return 0;
		}
	}

#if DEBUG_ENABLE_IPC_WARNINGS
	if (group_size > 0) {
		print_deadlock_info(cp, src_dst_e, group_size);
	}
#endif
	return group_size;
}

#if DEBUG_ENABLE_IPC_WARNINGS
static void print_deadlock_info(struct proc *cp, endpoint_t src_dst_e, int group_size)
{
	struct proc *processes[NR_PROCS + NR_TASKS];
	struct proc *xp;
	int i = 0;
	int src_dst_slot;
	
	processes[i++] = cp;
	while (src_dst_e != ANY && i < group_size) {
		okendpt(src_dst_e, &src_dst_slot);
		xp = proc_addr(src_dst_slot);
		processes[i++] = xp;
		src_dst_e = P_BLOCKEDON(xp);
	}
	
	printf("deadlock between these processes:\n");
	for(i = 0; i < group_size; i++) {
		printf(" %10s ", processes[i]->p_name);
	}
	printf("\n\n");
	for(i = 0; i < group_size; i++) {
		print_proc(processes[i]);
		proc_stacktrace(processes[i]);
	}
}
#endif

static int has_pending(sys_map_t *map, int src_p, int asynm)
{
	if (src_p != ANY) {
		return check_specific_source(map, src_p, asynm);
	}
	return find_any_source(map, asynm);
}

static int check_specific_source(sys_map_t *map, int src_p, int asynm)
{
	int src_id = nr_to_id(src_p);
	
	if (!get_sys_bit(*map, src_id)) {
		return NULL_PRIV_ID;
	}

#ifdef CONFIG_SMP
	struct proc *p = proc_addr(id_to_nr(src_id));
	if (asynm && RTS_ISSET(p, RTS_VMINHIBIT)) {
		p->p_misc_flags |= MF_SENDA_VM_MISS;
		return NULL_PRIV_ID;
	}
#endif
	
	return src_id;
}

static int find_any_source(sys_map_t *map, int asynm)
{
	for (int src_id = 0; src_id < NR_SYS_PROCS; src_id += BITCHUNK_BITS) {
		if (get_sys_bits(*map, src_id) == 0) {
			continue;
		}
		
		int result = scan_chunk(map, src_id, asynm);
		if (result != NULL_PRIV_ID) {
			return result;
		}
	}
	
	return NULL_PRIV_ID;
}

static int scan_chunk(sys_map_t *map, int start_id, int asynm)
{
	for (int src_id = start_id; src_id < NR_SYS_PROCS; src_id++) {
		if (!get_sys_bit(*map, src_id)) {
			continue;
		}
		
#ifdef CONFIG_SMP
		if (asynm) {
			struct proc *p = proc_addr(id_to_nr(src_id));
			if (RTS_ISSET(p, RTS_VMINHIBIT)) {
				p->p_misc_flags |= MF_SENDA_VM_MISS;
				continue;
			}
		}
#endif
		
		return src_id;
	}
	
	return NULL_PRIV_ID;
}

int has_pending_notify(struct proc *caller, int src_p)
{
    if (caller == NULL) {
        return 0;
    }
    
    struct priv *caller_priv = priv(caller);
    if (caller_priv == NULL) {
        return 0;
    }
    
    sys_map_t *map = &caller_priv->s_notify_pending;
    if (map == NULL) {
        return 0;
    }
    
    return has_pending(map, src_p, 0);
}

int has_pending_asend(struct proc *caller, int src_p)
{
	if (caller == NULL) {
		return 0;
	}
	
	sys_map_t *map = &priv(caller)->s_asyn_pending;
	return has_pending(map, src_p, 1);
}

void unset_notify_pending(struct proc *caller, int src_p)
{
	if (caller == NULL) {
		return;
	}
	
	struct priv *caller_priv = priv(caller);
	if (caller_priv == NULL) {
		return;
	}
	
	sys_map_t *map = &caller_priv->s_notify_pending;
	if (map == NULL) {
		return;
	}
	
	unset_sys_bit(*map, src_p);
}

int mini_send(register struct proc *caller_ptr, endpoint_t dst_e,
	message *m_ptr, const int flags)
{
	register struct proc *dst_ptr;
	register struct proc **xpp;
	int dst_p;
	int result;
	
	dst_p = _ENDPOINT_P(dst_e);
	dst_ptr = proc_addr(dst_p);

	if (RTS_ISSET(dst_ptr, RTS_NO_ENDPOINT)) {
		return EDEADSRCDST;
	}

	if (WILLRECEIVE(caller_ptr->p_endpoint, dst_ptr, (vir_bytes)m_ptr, NULL)) {
		result = handle_direct_delivery(caller_ptr, dst_ptr, m_ptr, flags);
	} else {
		result = handle_queued_send(caller_ptr, dst_ptr, dst_e, m_ptr, flags);
	}
	
	return result;
}

static int handle_direct_delivery(struct proc *caller_ptr, struct proc *dst_ptr,
	message *m_ptr, const int flags)
{
	int call;
	int copy_result;
	
	assert(!(dst_ptr->p_misc_flags & MF_DELIVERMSG));

	copy_result = copy_message_to_destination(dst_ptr, m_ptr, flags);
	if (copy_result != OK) {
		return copy_result;
	}

	dst_ptr->p_delivermsg.m_source = caller_ptr->p_endpoint;
	dst_ptr->p_misc_flags |= MF_DELIVERMSG;

	call = determine_call_type(caller_ptr, flags);
	IPC_STATUS_ADD_CALL(dst_ptr, call);

	if (dst_ptr->p_misc_flags & MF_REPLY_PEND) {
		dst_ptr->p_misc_flags &= ~MF_REPLY_PEND;
	}

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
	struct proc **xpp;
	int copy_result;
	
	if (flags & NON_BLOCKING) {
		return ENOTREADY;
	}

	if (deadlock(SEND, caller_ptr, dst_e)) {
		return ELOCKED;
	}

	copy_result = copy_message_to_sender(caller_ptr, m_ptr, flags);
	if (copy_result != OK) {
		return copy_result;
	}

	RTS_SET(caller_ptr, RTS_SENDING);
	caller_ptr->p_sendto_e = dst_e;

	assert(caller_ptr->p_q_link == NULL);
	
	xpp = &dst_ptr->p_caller_q;
	while (*xpp) {
		xpp = &(*xpp)->p_q_link;
	}
	*xpp = caller_ptr;

#if DEBUG_IPC_HOOK
	hook_ipc_msgsend(&caller_ptr->p_sendmsg, caller_ptr, dst_ptr);
#endif

	return OK;
}

static int copy_message_to_destination(struct proc *dst_ptr, message *m_ptr, const int flags)
{
	if (!(flags & FROM_KERNEL)) {
		if (copy_msg_from_user(m_ptr, &dst_ptr->p_delivermsg)) {
			return EFAULT;
		}
	} else {
		dst_ptr->p_delivermsg = *m_ptr;
		IPC_STATUS_ADD_FLAGS(dst_ptr, IPC_FLG_MSG_FROM_KERNEL);
	}
	return OK;
}

static int copy_message_to_sender(struct proc *caller_ptr, message *m_ptr, const int flags)
{
	if (!(flags & FROM_KERNEL)) {
		if (copy_msg_from_user(m_ptr, &caller_ptr->p_sendmsg)) {
			return EFAULT;
		}
	} else {
		caller_ptr->p_sendmsg = *m_ptr;
		caller_ptr->p_misc_flags |= MF_SENDING_FROM_KERNEL;
	}
	return OK;
}

static int determine_call_type(struct proc *caller_ptr, const int flags)
{
	if (caller_ptr->p_misc_flags & MF_REPLY_PEND) {
		return SENDREC;
	}
	if (flags & NON_BLOCKING) {
		return SENDNB;
	}
	return SEND;
}

static int check_pending_notifications(struct proc *caller_ptr, int src_p, endpoint_t src_e)
{
	int src_id;
	int src_proc_nr;
	endpoint_t sender_e;

	if (caller_ptr == NULL) {
		return 0;
	}

	src_id = has_pending_notify(caller_ptr, src_p);
	if (src_id == NULL_PRIV_ID) {
		return 0;
	}

	src_proc_nr = id_to_nr(src_id);
	if (src_proc_nr == NONE) {
		return 0;
	}

	sender_e = proc_addr(src_proc_nr)->p_endpoint;
	if (!CANRECEIVE(src_e, sender_e, caller_ptr, 0, &m_notify_buff)) {
		return 0;
	}

	if ((caller_ptr->p_misc_flags & MF_DELIVERMSG) != 0) {
		return 0;
	}

	if (src_e != ANY && sender_e != src_e) {
		return 0;
	}

	unset_notify_pending(caller_ptr, src_id);
	BuildNotifyMessage(&caller_ptr->p_delivermsg, src_proc_nr, caller_ptr);
	caller_ptr->p_delivermsg.m_source = sender_e;
	caller_ptr->p_misc_flags |= MF_DELIVERMSG;
	IPC_STATUS_ADD_CALL(caller_ptr, NOTIFY);

	return 1;
}

static int check_async_messages(struct proc *caller_ptr, int src_p, endpoint_t src_e)
{
    if (caller_ptr == NULL) {
        return 0;
    }

    if (has_pending_asend(caller_ptr, src_p) == NULL_PRIV_ID) {
        return 0;
    }

    int result = (src_p != ANY) 
        ? try_one(src_e, proc_addr(src_p), caller_ptr)
        : try_async(caller_ptr);

    if (result != OK) {
        return 0;
    }

    IPC_STATUS_ADD_CALL(caller_ptr, SENDA);
    return 1;
}

static int check_caller_queue(struct proc *caller_ptr, endpoint_t src_e)
{
	struct proc **xpp = &caller_ptr->p_caller_q;
	
	while (*xpp != NULL) {
		struct proc *sender = *xpp;
		endpoint_t sender_e = sender->p_endpoint;

		if (CANRECEIVE(src_e, sender_e, caller_ptr, 0, &sender->p_sendmsg)) {
			assert(!RTS_ISSET(sender, RTS_SLOT_FREE));
			assert(!RTS_ISSET(sender, RTS_NO_ENDPOINT));
			assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));
			
			caller_ptr->p_delivermsg = sender->p_sendmsg;
			caller_ptr->p_delivermsg.m_source = sender->p_endpoint;
			caller_ptr->p_misc_flags |= MF_DELIVERMSG;
			
			*xpp = sender->p_q_link;
			sender->p_q_link = NULL;
			
			return OK;
		}
		
		xpp = &sender->p_q_link;
	}
	
	return EAGAIN;
}