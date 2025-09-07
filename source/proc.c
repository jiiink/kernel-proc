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
        int i, c;
        int p_z = 0;

        if (n > 999) 
                n = 999; 

        name[0] = 'i'; 
        name[1] = 'd'; 
        name[2] = 'l'; 
        name[3] = 'e'; 

        for (i = 4, c = 100; c > 0; c /= 10) {
                int digit;

                digit = n / c;  
                n -= digit * c;  

                if (p_z || digit != 0 || c == 1) {
                        p_z = 1;
                        name[i++] = '0' + digit;
                }   
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

void proc_init(void)
{
	struct proc * rp;
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
		struct proc * ip = get_cpu_var_ptr(i, idle_proc);
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
	struct proc * p;

	p = get_cpulocal_var(proc_ptr) = get_cpulocal_var_ptr(idle_proc);
	if (priv(p)->s_flags & BILLABLE)
		get_cpulocal_var(bill_ptr) = p;

	switch_address_space_idle();

#ifdef CONFIG_SMP
	get_cpulocal_var(cpu_is_idle) = 1;
	if (cpuid != bsp_cpu_id)
		stop_local_timer();
	else
#endif
	{
		restart_local_timer();
	}

	context_stop(proc_addr(KERNEL));
#if !SPROFILE
	halt_cpu();
#else
	if (!sprofiling)
		halt_cpu();
	else {
		volatile int * v;

		v = get_cpulocal_var_ptr(idle_interrupted);
		interrupts_enable();
		while (!*v)
			arch_pause();
		interrupts_disable();
		*v = 0;
	}
#endif
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

        if(!(caller->p_vmrequest.nextrequestor = vmrequest))
                if(OK != send_sig(VM_PROC_NR, SIGKMEM))
                        panic("send_sig failed");
        vmrequest = caller;
}

static void delivermsg(struct proc *rp)
{
        assert(!RTS_ISSET(rp, RTS_VMREQUEST));
        assert(rp->p_misc_flags & MF_DELIVERMSG);
        assert(rp->p_delivermsg.m_source != NONE);

        if (copy_msg_to_user(&rp->p_delivermsg,
                                (message *) rp->p_delivermsg_vir)) {
                if(rp->p_misc_flags & MF_MSGFAILED) {
                        printf("WARNING wrong user pointer 0x%08lx from "
                                "process %s / %d\n",
                                rp->p_delivermsg_vir,
                                rp->p_name,
                                rp->p_endpoint);
                        cause_sig(rp->p_nr, SIGSEGV);
                } else {
                        vm_suspend(rp, rp, rp->p_delivermsg_vir,
                                sizeof(message), VMSTYPE_DELIVERMSG, 1);
                        rp->p_misc_flags |= MF_MSGFAILED;
                }
        } else {
                rp->p_delivermsg.m_source = NONE;
                rp->p_misc_flags &= ~(MF_DELIVERMSG|MF_MSGFAILED);

                if(!(rp->p_misc_flags & MF_CONTEXT_SET)) {
                        rp->p_reg.retreg = OK;
                }
        }
}

static void handle_misc_flags(struct proc *p)
{
	if (p->p_misc_flags & MF_KCALL_RESUME) {
		kernel_call_resume(p);
	}
	else if (p->p_misc_flags & MF_DELIVERMSG) {
		TRACE(VF_SCHEDULING, printf("delivering to %s / %d\n",
			p->p_name, p->p_endpoint););
		delivermsg(p);
	}
	else if (p->p_misc_flags & MF_SC_DEFER) {
		assert (!(p->p_misc_flags & MF_SC_ACTIVE));
		arch_do_syscall(p);
		if ((p->p_misc_flags & MF_SIG_DELAY) &&
				!RTS_ISSET(p, RTS_SENDING))
			sig_delay_done(p);
	}
	else if ((p->p_misc_flags & MF_SC_TRACE) && 
	         (p->p_misc_flags & MF_SC_ACTIVE)) {
		p->p_misc_flags &= ~(MF_SC_TRACE | MF_SC_ACTIVE);
		cause_sig(proc_nr(p), SIGTRAP);
	}
	else if (p->p_misc_flags & MF_SC_ACTIVE) {
		p->p_misc_flags &= ~MF_SC_ACTIVE;
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
	if (proc_is_preempted(p)) {
		p->p_rts_flags &= ~RTS_PREEMPTED;
		if (proc_is_runnable(p)) {
			if (p->p_cpu_time_left)
				enqueue_head(p);
			else
				enqueue(p);
		}
	}

	while (!(p = pick_proc())) {
		idle();
	}

	get_cpulocal_var(proc_ptr) = p;

#ifdef CONFIG_SMP
	if (p->p_misc_flags & MF_FLUSH_TLB && get_cpulocal_var(ptproc) == p)
		tlb_must_refresh = 1;
#endif
	switch_address_space(p);

check_misc_flags:
	assert(p);
	assert(proc_is_runnable(p));
	while (p->p_misc_flags &
		(MF_KCALL_RESUME | MF_DELIVERMSG |
		 MF_SC_DEFER | MF_SC_TRACE | MF_SC_ACTIVE)) {

		assert(proc_is_runnable(p));
		handle_misc_flags(p);

		if (!proc_is_runnable(p))
			goto not_runnable_pick_new;
	}

	if (!p->p_cpu_time_left)
		proc_no_time(p);

	if (!proc_is_runnable(p))
		goto not_runnable_pick_new;

	TRACE(VF_SCHEDULING, printf("cpu %d starting %s / %d "
				"pc 0x%08x\n",
		cpuid, p->p_name, p->p_endpoint, p->p_reg.pc););
#if DEBUG_TRACE
	p->p_schedules++;
#endif

	p = arch_finish_switch_to_user();
	assert(p->p_cpu_time_left);

	context_stop(proc_addr(KERNEL));

	if (get_cpulocal_var(fpu_owner) != p)
		enable_fpu_exception();
	else
		disable_fpu_exception();

	p->p_misc_flags &= ~MF_CONTEXT_SET;

#if defined(__i386__)
  	assert(p->p_seg.p_cr3 != 0);
#elif defined(__arm__)
	assert(p->p_seg.p_ttbr != 0);
#endif
#ifdef CONFIG_SMP
	if (p->p_misc_flags & MF_FLUSH_TLB) {
		if (tlb_must_refresh)
			refresh_tlb();
		p->p_misc_flags &= ~MF_FLUSH_TLB;
	}
#endif
	
	restart_local_timer();
	
	restore_user_context(p);
	NOT_REACHABLE;
}

static int validate_ipc_call(struct proc * caller_ptr, int call_nr, 
                              endpoint_t src_dst_e, int *src_dst_p)
{
	char *callname;

	if (call_nr < 0 || call_nr > IPCNO_HIGHEST || call_nr >= 32
	    || !(callname = ipc_call_names[call_nr])) {
#if DEBUG_ENABLE_IPC_WARNINGS
		printf("sys_call: trap %d not allowed, caller %d, src_dst %d\n", 
		    call_nr, proc_nr(caller_ptr), src_dst_e);
#endif
		return(ETRAPDENIED);
	}

	if (src_dst_e == ANY) {
		if (call_nr != RECEIVE)
			return EINVAL;
		*src_dst_p = (int) src_dst_e;
	} else {
		if(!isokendpt(src_dst_e, src_dst_p))
			return EDEADSRCDST;

		if (call_nr != RECEIVE) {
			if (!may_send_to(caller_ptr, *src_dst_p)) {
#if DEBUG_ENABLE_IPC_WARNINGS
				printf(
				"sys_call: ipc mask denied %s from %d to %d\n",
					callname,
					caller_ptr->p_endpoint, src_dst_e);
#endif
				return(ECALLDENIED);
			}
		}
	}

	if (!(priv(caller_ptr)->s_trap_mask & (1 << call_nr))) {
#if DEBUG_ENABLE_IPC_WARNINGS
		printf("sys_call: %s not allowed, caller %d, src_dst %d\n", 
		    callname, proc_nr(caller_ptr), *src_dst_p);
#endif
		return(ETRAPDENIED);
	}

	if (call_nr != SENDREC && call_nr != RECEIVE && iskerneln(*src_dst_p)) {
#if DEBUG_ENABLE_IPC_WARNINGS
		printf("sys_call: trap %s not allowed, caller %d, src_dst %d\n",
		     callname, proc_nr(caller_ptr), src_dst_e);
#endif
		return(ETRAPDENIED);
	}

	return OK;
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
		caller_ptr->p_misc_flags |= MF_REPLY_PEND;
		result = mini_send(caller_ptr, src_dst_e, m_ptr, 0);
		if (result != OK)
			break;
		/* fall through */
	case RECEIVE:			
		if (call_nr == RECEIVE) {
			caller_ptr->p_misc_flags &= ~MF_REPLY_PEND;
			IPC_STATUS_CLEAR(caller_ptr);
		}
		result = mini_receive(caller_ptr, src_dst_e, m_ptr, 0);
		break;
	case SEND:			
		result = mini_send(caller_ptr, src_dst_e, m_ptr, 0);
		break;
	case NOTIFY:
		result = mini_notify(caller_ptr, src_dst_e);
		break;
	case SENDNB:
		result = mini_send(caller_ptr, src_dst_e, m_ptr, NON_BLOCKING);
		break;
	default:
		result = EBADCALL;
	}

	return(result);
}

static void handle_syscall_trace(struct proc *caller_ptr, reg_t r1, reg_t r2, reg_t r3)
{
	if ((caller_ptr->p_misc_flags & (MF_SC_TRACE | MF_SC_DEFER)) == MF_SC_TRACE) {
		caller_ptr->p_misc_flags &= ~MF_SC_TRACE;
		assert(!(caller_ptr->p_misc_flags & MF_SC_DEFER));
		caller_ptr->p_misc_flags |= MF_SC_DEFER;
		caller_ptr->p_defer.r1 = r1;
		caller_ptr->p_defer.r2 = r2;
		caller_ptr->p_defer.r3 = r3;

		cause_sig(proc_nr(caller_ptr), SIGTRAP);
	} else {
		caller_ptr->p_misc_flags &= ~MF_SC_DEFER;
		assert (!(caller_ptr->p_misc_flags & MF_SC_ACTIVE));
		caller_ptr->p_misc_flags |= MF_SC_ACTIVE;
	}
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
		if (caller_ptr->p_misc_flags & MF_SC_DEFER)
			return prev_result;
	}

	if(caller_ptr->p_misc_flags & MF_DELIVERMSG) {
		panic("sys_call: MF_DELIVERMSG on for %s / %d\n",
			caller_ptr->p_name, caller_ptr->p_endpoint);
	}

	switch(call_nr) {
	case SENDREC:
	case SEND:			
	case RECEIVE:			
	case NOTIFY:
	case SENDNB:
		caller_ptr->p_accounting.ipc_sync++;
		return do_sync_ipc(caller_ptr, call_nr, (endpoint_t) r2,
				(message *) r3);
	case SENDA:
		{
		size_t msg_size = (size_t) r2;

		caller_ptr->p_accounting.ipc_async++;

		if (msg_size > 16*(NR_TASKS + NR_PROCS))
			return EDOM;
		return mini_senda(caller_ptr, (asynmsg_t *) r3, msg_size);
		}
	case MINIX_KERNINFO:
		if(!minix_kerninfo_user) {
			return EBADCALL;
		}
		arch_set_secondary_ipc_return(caller_ptr, minix_kerninfo_user);
		return OK;
	default:
		return EBADCALL;
	}
}

static int check_deadlock_cycle(struct proc *cp, endpoint_t src_dst_e)
{
	struct proc *xp;
	int group_size = 1;
	int src_dst_slot;

	while (src_dst_e != ANY) {
		okendpt(src_dst_e, &src_dst_slot);
		xp = proc_addr(src_dst_slot);
		assert(proc_ptr_ok(xp));
		assert(!RTS_ISSET(xp, RTS_SLOT_FREE));
		group_size++;

		if((src_dst_e = P_BLOCKEDON(xp)) == NONE)
			return 0;

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
	return group_size;
}

static int has_pending(sys_map_t *map, int src_p, int asynm)
{
	int src_id;
	sys_id_t id = NULL_PRIV_ID;
#ifdef CONFIG_SMP
	struct proc * p;
#endif

	if (src_p != ANY) {
		src_id = nr_to_id(src_p);
		if (get_sys_bit(*map, src_id)) {
#ifdef CONFIG_SMP
			p = proc_addr(id_to_nr(src_id));
			if (asynm && RTS_ISSET(p, RTS_VMINHIBIT))
				p->p_misc_flags |= MF_SENDA_VM_MISS;
			else
#endif
				id = src_id;
		}
	} else {
		for (src_id = 0; src_id < NR_SYS_PROCS; src_id += BITCHUNK_BITS) {
			if (get_sys_bits(*map, src_id) != 0) {
#ifdef CONFIG_SMP
				while (src_id < NR_SYS_PROCS) {
					while (!get_sys_bit(*map, src_id)) {
						if (src_id == NR_SYS_PROCS)
							goto quit_search;
						src_id++;
					}
					p = proc_addr(id_to_nr(src_id));
					if (asynm && RTS_ISSET(p, RTS_VMINHIBIT)) {
						p->p_misc_flags |= MF_SENDA_VM_MISS;
						src_id++;
					} else
						goto quit_search;
				}
#else
				while (!get_sys_bit(*map, src_id)) src_id++;
				goto quit_search;
#endif
			}
		}

quit_search:
		if (src_id < NR_SYS_PROCS)
			id = src_id;
	}

	return(id);
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
	register struct proc **xpp;
	int dst_p;
	dst_p = _ENDPOINT_P(dst_e);
	dst_ptr = proc_addr(dst_p);

	if (RTS_ISSET(dst_ptr, RTS_NO_ENDPOINT))
		return EDEADSRCDST;

	if (WILLRECEIVE(caller_ptr->p_endpoint, dst_ptr, (vir_bytes)m_ptr, NULL)) {
		int call;
		assert(!(dst_ptr->p_misc_flags & MF_DELIVERMSG));	

		if (!(flags & FROM_KERNEL)) {
			if(copy_msg_from_user(m_ptr, &dst_ptr->p_delivermsg))
				return EFAULT;
		} else {
			dst_ptr->p_delivermsg = *m_ptr;
			IPC_STATUS_ADD_FLAGS(dst_ptr, IPC_FLG_MSG_FROM_KERNEL);
		}

		dst_ptr->p_delivermsg.m_source = caller_ptr->p_endpoint;
		dst_ptr->p_misc_flags |= MF_DELIVERMSG;

		call = (caller_ptr->p_misc_flags & MF_REPLY_PEND ? SENDREC
			: (flags & NON_BLOCKING ? SENDNB : SEND));
		IPC_STATUS_ADD_CALL(dst_ptr, call);

		if (dst_ptr->p_misc_flags & MF_REPLY_PEND)
			dst_ptr->p_misc_flags &= ~MF_REPLY_PEND;

		RTS_UNSET(dst_ptr, RTS_RECEIVING);

#if DEBUG_IPC_HOOK
		hook_ipc_msgsend(&dst_ptr->p_delivermsg, caller_ptr, dst_ptr);
		hook_ipc_msgrecv(&dst_ptr->p_delivermsg, caller_ptr, dst_ptr);
#endif
	} else {
		if(flags & NON_BLOCKING)
			return(ENOTREADY);

		if (deadlock(SEND, caller_ptr, dst_e))
			return(ELOCKED);

		if (!(flags & FROM_KERNEL)) {
			if(copy_msg_from_user(m_ptr, &caller_ptr->p_sendmsg))
				return EFAULT;
		} else {
			caller_ptr->p_sendmsg = *m_ptr;
			caller_ptr->p_misc_flags |= MF_SENDING_FROM_KERNEL;
		}

		RTS_SET(caller_ptr, RTS_SENDING);
		caller_ptr->p_sendto_e = dst_e;

		assert(caller_ptr->p_q_link == NULL);
		xpp = &dst_ptr->p_caller_q;
		while (*xpp) xpp = &(*xpp)->p_q_link;	
		*xpp = caller_ptr;

#if DEBUG_IPC_HOOK
		hook_ipc_msgsend(&caller_ptr->p_sendmsg, caller_ptr, dst_ptr);
#endif
	}
	return(OK);
}

static int check_pending_notifications(struct proc *caller_ptr, int src_p, endpoint_t src_e)
{
	int src_id = has_pending_notify(caller_ptr, src_p);
	
	if (src_id == NULL_PRIV_ID)
		return 0;
		
	int src_proc_nr = id_to_nr(src_id);
	endpoint_t sender_e = proc_addr(src_proc_nr)->p_endpoint;
	
	if (!CANRECEIVE(src_e, sender_e, caller_ptr, 0, &m_notify_buff))
		return 0;

#if DEBUG_ENABLE_IPC_WARNINGS
	if(src_proc_nr == NONE) {
		printf("mini_receive: sending notify from NONE\n");
	}
#endif
	assert(src_proc_nr != NONE);
	unset_notify_pending(caller_ptr, src_id);

	assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));	
	assert(src_e == ANY || sender_e == src_e);

	BuildNotifyMessage(&caller_ptr->p_delivermsg, src_proc_nr, caller_ptr);
	caller_ptr->p_delivermsg.m_source = sender_e;
	caller_ptr->p_misc_flags |= MF_DELIVERMSG;

	IPC_STATUS_ADD_CALL(caller_ptr, NOTIFY);
	return 1;
}

static int check_async_messages(struct proc *caller_ptr, int src_p, endpoint_t src_e)
{
	if (has_pending_asend(caller_ptr, src_p) == NULL_PRIV_ID)
		return 0;
		
	int r;
	if (src_p != ANY)
		r = try_one(src_e, proc_addr(src_p), caller_ptr);
	else
		r = try_async(caller_ptr);

	if (r == OK) {
		IPC_STATUS_ADD_CALL(caller_ptr, SENDA);
		return 1;
	}
	return 0;
}

static int check_caller_queue(struct proc *caller_ptr, endpoint_t src_e)
{
	struct proc **xpp = &caller_ptr->p_caller_q;
	
	while (*xpp) {
		struct proc * sender = *xpp;
		endpoint_t sender_e = sender->p_endpoint;

		if (CANRECEIVE(src_e, sender_e, caller_ptr, 0, &sender->p_sendmsg)) {
			int call;
			assert(!RTS_ISSET(sender, RTS_SLOT_FREE));
			assert(!RTS_ISSET(sender, RTS_NO_ENDPOINT));

			assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));
			caller_ptr->p_delivermsg = sender->p_sendmsg;
			caller_ptr->p_delivermsg.