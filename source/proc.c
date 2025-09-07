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

static inline void build_notify_message(message *m_ptr, int src, struct proc *dst_ptr)
{
	memset(m_ptr, 0, sizeof(*m_ptr));
	m_ptr->m_type = NOTIFY_MESSAGE;
	m_ptr->m_notify.timestamp = get_monotonic();
	switch (src) {
	case HARDWARE:
		m_ptr->m_notify.interrupts = priv(dst_ptr)->s_int_pending;
		priv(dst_ptr)->s_int_pending = 0;
		break;
	case SYSTEM:
		memcpy(&m_ptr->m_notify.sigset, &priv(dst_ptr)->s_sig_pending,
			sizeof(sigset_t));
		sigemptyset(&priv(dst_ptr)->s_sig_pending);
		break;
	}
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

	caller->p_vmrequest.nextrequestor = vmrequest;
	if(!vmrequest) {
		if(OK != send_sig(VM_PROC_NR, SIGKMEM))
			panic("send_sig failed");
	}
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

static int handle_proc_misc_flags(struct proc *p)
{
	while (p->p_misc_flags &
		(MF_KCALL_RESUME | MF_DELIVERMSG | MF_SC_DEFER | MF_SC_TRACE | MF_SC_ACTIVE)) {

		assert(proc_is_runnable(p));
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
			if ((p->p_misc_flags & MF_SIG_DELAY) && !RTS_ISSET(p, RTS_SENDING))
				sig_delay_done(p);
		}
		else if (p->p_misc_flags & MF_SC_TRACE) {
			if (!(p->p_misc_flags & MF_SC_ACTIVE))
				break;

			p->p_misc_flags &= ~(MF_SC_TRACE | MF_SC_ACTIVE);
			cause_sig(proc_nr(p), SIGTRAP);
		}
		else if (p->p_misc_flags & MF_SC_ACTIVE) {
			p->p_misc_flags &= ~MF_SC_ACTIVE;
			break;
		}

		if (!proc_is_runnable(p))
			return 0;
	}
	return 1;
}

void switch_to_user(void)
{
	struct proc * p;
#ifdef CONFIG_SMP
	int tlb_must_refresh = 0;
#endif

	for(;;) {
		p = get_cpulocal_var(proc_ptr);
		if (!proc_is_runnable(p)) {
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
		}

		assert(p);
		assert(proc_is_runnable(p));

		if (!handle_proc_misc_flags(p)) {
			continue;
		}

		if (!p->p_cpu_time_left) {
			proc_no_time(p);
			if (!proc_is_runnable(p)) {
				continue;
			}
		}

		if (proc_is_runnable(p)) {
			break;
		}
	}

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

static int do_sync_ipc(struct proc * caller_ptr,
			int call_nr,
			endpoint_t src_dst_e,
			message *m_ptr)
{
	int result = OK;
	int src_dst_p;
	char *callname;

	if (call_nr < 0 || call_nr > IPCNO_HIGHEST || !(callname = ipc_call_names[call_nr])) {
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
		src_dst_p = (int) src_dst_e;
	} else {
		if (!isokendpt(src_dst_e, &src_dst_p)) {
			return EDEADSRCDST;
		}
		if (call_nr != RECEIVE) {
			if (!may_send_to(caller_ptr, src_dst_p)) {
#if DEBUG_ENABLE_IPC_WARNINGS
				printf("sys_call: ipc mask denied %s from %d to %d\n",
					callname, caller_ptr->p_endpoint, src_dst_e);
#endif
				return ECALLDENIED;
			}
		}
	}

	if (!(priv(caller_ptr)->s_trap_mask & (1 << call_nr))) {
#if DEBUG_ENABLE_IPC_WARNINGS
		printf("sys_call: %s not allowed, caller %d, src_dst %d\n", 
			callname, proc_nr(caller_ptr), src_dst_p);
#endif
		return ETRAPDENIED;
	}

	if (call_nr != SENDREC && call_nr != RECEIVE && iskerneln(src_dst_p)) {
#if DEBUG_ENABLE_IPC_WARNINGS
		printf("sys_call: trap %s not allowed, caller %d, src_dst %d\n",
			callname, proc_nr(caller_ptr), src_dst_e);
#endif
		return ETRAPDENIED;
	}
	
	switch (call_nr) {
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
	}
	
	return result;
}

int do_ipc(reg_t r1, reg_t r2, reg_t r3)
{
	struct proc *const caller_ptr = get_cpulocal_var(proc_ptr);
	int call_nr = (int) r1;

	assert(!RTS_ISSET(caller_ptr, RTS_SLOT_FREE));

	kbill_ipc = caller_ptr;

	if (caller_ptr->p_misc_flags & (MF_SC_TRACE | MF_SC_DEFER)) {
		if ((caller_ptr->p_misc_flags & (MF_SC_TRACE | MF_SC_DEFER)) ==
							MF_SC_TRACE) {
			caller_ptr->p_misc_flags &= ~MF_SC_TRACE;
			assert(!(caller_ptr->p_misc_flags & MF_SC_DEFER));
			caller_ptr->p_misc_flags |= MF_SC_DEFER;
			caller_ptr->p_defer.r1 = r1;
			caller_ptr->p_defer.r2 = r2;
			caller_ptr->p_defer.r3 = r3;

			cause_sig(proc_nr(caller_ptr), SIGTRAP);

			return caller_ptr->p_reg.retreg;
		}
		caller_ptr->p_misc_flags &= ~MF_SC_DEFER;
		assert (!(caller_ptr->p_misc_flags & MF_SC_ACTIVE));
		caller_ptr->p_misc_flags |= MF_SC_ACTIVE;
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

static int deadlock(
  int function,
  register struct proc *cp,
  endpoint_t src_dst_e
)
{
	register struct proc *xp;
	int group_size = 1;
#if DEBUG_ENABLE_IPC_WARNINGS
	static struct proc *processes[NR_PROCS + NR_TASKS];
	processes[0] = cp;
#endif

	while (src_dst_e != ANY) {
		int src_dst_slot;
		okendpt(src_dst_e, &src_dst_slot);
		xp = proc_addr(src_dst_slot);
		assert(proc_ptr_ok(xp));
		assert(!RTS_ISSET(xp, RTS_SLOT_FREE));
#if DEBUG_ENABLE_IPC_WARNINGS
		processes[group_size] = xp;
#endif
		group_size ++;

		if((src_dst_e = P_BLOCKEDON(xp)) == NONE)
			return 0;

		if (src_dst_e == cp->p_endpoint) {
			if (group_size == 2) {
				if ((xp->p_rts_flags ^ (function << 2)) & RTS_SENDING) { 
					return 0;
				}
			}
#if DEBUG_ENABLE_IPC_WARNINGS
			{
				int i;
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
	}
	return 0;
}

static int has_pending(sys_map_t *map, int src_p, int asynm)
{
	sys_id_t id = NULL_PRIV_ID;

	if (src_p != ANY) {
		int src_id = nr_to_id(src_p);
		if (get_sys_bit(*map, src_id)) {
#ifdef CONFIG_SMP
			struct proc *p = proc_addr(id_to_nr(src_id));
			if (!asynm || !RTS_ISSET(p, RTS_VMINHIBIT)) {
				id = src_id;
			} else {
				p->p_misc_flags |= MF_SENDA_VM_MISS;
			}
#else
			id = src_id;
#endif
		}
	} else {
		int src_id;
		for (src_id = 0; src_id < NR_SYS_PROCS; src_id++) {
			if (get_sys_bit(*map, src_id)) {
#ifdef CONFIG_SMP
				struct proc *p = proc_addr(id_to_nr(src_id));
				if (asynm && RTS_ISSET(p, RTS_VMINHIBIT)) {
					p->p_misc_flags |= MF_SENDA_VM_MISS;
					continue;
				}
#endif
				id = src_id;
				break;
			}
		}
	}

	return id;
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

int mini_send(
  register struct proc *caller_ptr,
  endpoint_t dst_e,
  message *m_ptr,
  const int flags
)
{
	register struct proc *dst_ptr;
	register struct proc **xpp;
	int dst_p = _ENDPOINT_P(dst_e);
	dst_ptr = proc_addr(dst_p);

	if (RTS_ISSET(dst_ptr, RTS_NO_ENDPOINT)) {
		return EDEADSRCDST;
	}

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
		if(flags & NON_BLOCKING) {
			return ENOTREADY;
		}

		if (deadlock(SEND, caller_ptr, dst_e)) {
			return ELOCKED;
		}

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
	return OK;
}

static int mini_receive(struct proc * caller_ptr,
			endpoint_t src_e,
			message * m_buff_usr,
			const int flags)
{
	register struct proc **xpp;
	int src_id, src_proc_nr, src_p;
	endpoint_t sender_e;

	assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));

	caller_ptr->p_delivermsg_vir = (vir_bytes) m_buff_usr;

	if(src_e == ANY) {
		src_p = ANY;
	} else {
		if (!isokendpt(src_e, &src_p)) return EDEADSRCDST;
		if (RTS_ISSET(proc_addr(src_p), RTS_NO_ENDPOINT)) {
			return EDEADSRCDST;
		}
	}

	if (!RTS_ISSET(caller_ptr, RTS_SENDING)) {
		if (!(caller_ptr->p_misc_flags & MF_REPLY_PEND)) {
			src_id = has_pending_notify(caller_ptr, src_p);
			if(src_id != NULL_PRIV_ID) {
				src_proc_nr = id_to_nr(src_id);
				sender_e = proc_addr(src_proc_nr)->p_endpoint;

				if (CANRECEIVE(src_e, sender_e, caller_ptr, 0, &m_notify_buff)) {
					assert(src_proc_nr != NONE);
					unset_notify_pending(caller_ptr, src_id);
					assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));	
					assert(src_e == ANY || sender_e == src_e);
					build_notify_message(&caller_ptr->p_delivermsg, src_proc_nr, caller_ptr);
					caller_ptr->p_delivermsg.m_source = sender_e;
					caller_ptr->p_misc_flags |= MF_DELIVERMSG;
					IPC_STATUS_ADD_CALL(caller_ptr, NOTIFY);
					if (caller_ptr->p_misc_flags & MF_REPLY_PEND)
						caller_ptr->p_misc_flags &= ~MF_REPLY_PEND;
					return OK;
				}
			}
		}

		if (has_pending_asend(caller_ptr, src_p) != NULL_PRIV_ID) {
			int r = (src_p != ANY) ? try_one(src_e, proc_addr(src_p), caller_ptr) : try_async(caller_ptr);
			if (r == OK) {
				IPC_STATUS_ADD_CALL(caller_ptr, SENDA);
				if (caller_ptr->p_misc_flags & MF_REPLY_PEND)
					caller_ptr->p_misc_flags &= ~MF_REPLY_PEND;
				return OK;
			}
		}

		xpp = &caller_ptr->p_caller_q;
		while (*xpp) {
			struct proc * sender = *xpp;
			if (CANRECEIVE(src_e, sender->p_endpoint, caller_ptr, 0, &sender->p_sendmsg)) {
				int call;
				assert(!RTS_ISSET(sender, RTS_SLOT_FREE));
				assert(!RTS_ISSET(sender, RTS_NO_ENDPOINT));

				assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));
				caller_ptr->p_delivermsg = sender->p_sendmsg;
				caller_ptr->p_delivermsg.m_source = sender->p_endpoint;
				caller_ptr->p_misc_flags |= MF_DELIVERMSG;
				RTS_UNSET(sender, RTS_SENDING);

				call = (sender->p_misc_flags & MF_REPLY_PEND ? SENDREC : SEND);
				IPC_STATUS_ADD_CALL(caller_ptr, call);

				if (sender->p_misc_flags & MF_SENDING_FROM_KERNEL) {
					IPC_STATUS_ADD_FLAGS(caller_ptr, IPC_FLG_MSG_FROM_KERNEL);
					sender->p_misc_flags &= ~MF_SENDING_FROM_KERNEL;
				}
				if (sender->p_misc_flags & MF_SIG_DELAY)
					sig_delay_done(sender);

#if DEBUG_IPC_HOOK
				hook_ipc_msgrecv(&caller_ptr->p_delivermsg, *xpp, caller_ptr);
#endif
				*xpp = sender->p_q_link;
				sender->p_q_link = NULL;

				if (caller_ptr->p_misc_flags & MF_REPLY_PEND)
					caller_ptr->p_misc_flags &= ~MF_REPLY_PEND;
				return OK;
			}
			xpp = &sender->p_q_link;
		}
	}

	if (!(flags & NON_BLOCKING)) {
		if (deadlock(RECEIVE, caller_ptr, src_e)) {
			return ELOCKED;
		}
		caller_ptr->p_getfrom_e = src_e;		
		RTS_SET(caller_ptr, RTS_RECEIVING);
		return OK;
	} else {
		return ENOTREADY;
	}
}

int mini_notify(
  const struct proc *caller_ptr,
  endpoint_t dst_e
)
{
	register struct proc *dst_ptr;
	int src_id;
	int dst_p;

	if (!isokendpt(dst_e, &dst_p)) {
		util_stacktrace();
		printf("mini_notify: bogus endpoint %d\n", dst_e);
		return EDEADSRCDST;
	}

	dst_ptr = proc_addr(dst_p);

	if (WILLRECEIVE(caller_ptr->p_endpoint, dst_ptr, 0, &m_notify_buff) &&
		!(dst_ptr->p_misc_flags & MF_REPLY_PEND)) {
		assert(!(dst_ptr->p_misc_flags & MF_DELIVERMSG));

		build_notify_message(&dst_ptr->p_delivermsg, proc_nr(caller_ptr), dst_ptr);
		dst_ptr->p_delivermsg.m_source = caller_ptr->p_endpoint;
		dst_ptr->p_misc_flags |= MF_DELIVERMSG;

		IPC_STATUS_ADD_CALL(dst_ptr, NOTIFY);
		RTS_UNSET(dst_ptr, RTS_RECEIVING);

		return OK;
	} 

	src_id = priv(caller_ptr)->s_id;
	set_sys_bit(priv(dst_ptr)->s_notify_pending, src_id); 
	return OK;
}

static inline void asyn_complain(const struct proc *caller, int entry, const char *field)
{
	printf("kernel:%s:%d: asyn failed for %s in %s (%d/%zu, tab 0x%lx)\n",
		__FILE__,__LINE__, field, caller->p_name, entry,
		priv(caller)->s_asynsize, priv(caller)->s_asyntab);
}

static inline int asyn_retrieve_entry(struct proc *caller_ptr, vir_bytes table_v,
	int entry, asynmsg_t *tabent)
{
	if (data_copy(caller_ptr->p_endpoint, table_v + (entry) * sizeof(asynmsg_t),
		KERNEL, (vir_bytes)tabent, sizeof(*tabent)) != OK) {
		asyn_complain(caller_ptr, entry, "message entry");
		return EFAULT;
	}
	if (tabent->dst == SELF) {
		tabent->dst = caller_ptr->p_endpoint;
	}
	return OK;
}

static inline void asyn_insert_entry(struct proc *caller_ptr, vir_bytes table_v,
	int entry, const asynmsg_t *tabent)
{
	if (data_copy(KERNEL, (vir_bytes)tabent, caller_ptr->p_endpoint,
		table_v + (entry) * sizeof(asynmsg_t), sizeof(*tabent)) != OK) {
		asyn_complain(caller_ptr, entry, "message entry");
	}
}

int try_deliver_senda(struct proc *caller_ptr,
				asynmsg_t *table,
				size_t size)
{
	int r, dst_p, done, do_notify;
	unsigned int i;
	struct proc *dst_ptr;
	struct priv *privp;
	asynmsg_t tabent;
	const vir_bytes table_v = (vir_bytes) table;

	privp = priv(caller_ptr);
	privp->s_asyntab = -1;
	privp->s_asynsize = 0;
	privp->s_asynendpoint = caller_ptr->p_endpoint;

	if (size == 0) return OK;

	do_notify = FALSE;
	done = TRUE;

	if (size > 16*(NR_TASKS + NR_PROCS)) {
		return EDOM;
	}

	for (i = 0; i < size; i++) {
		if (asyn_retrieve_entry(caller_ptr, table_v, i, &tabent) != OK) {
			r = EFAULT;
			goto asyn_error_in_loop;
		}

		if (tabent.flags == 0) continue;
		if (tabent.flags & ~(AMF_VALID|AMF_DONE|AMF_NOTIFY|AMF_NOREPLY|AMF_NOTIFY_ERR)) {
			r = EINVAL;
			goto asyn_error_in_loop;
		}
		if (!(tabent.flags & AMF_VALID)) {
			r = EINVAL;
			goto asyn_error_in_loop;
		}
		if (tabent.flags & AMF_DONE) continue;

		r = OK;
		if (!isokendpt(tabent.dst, &dst_p)) r = EDEADSRCDST;
		else if (iskerneln(dst_p)) r = ECALLDENIED;
		else if (!may_asynsend_to(caller_ptr, dst_p)) r = ECALLDENIED;
		else {
			dst_ptr = proc_addr(dst_p);
			if (RTS_ISSET(dst_ptr, RTS_NO_ENDPOINT)) r = EDEADSRCDST;
		}

		if (r == OK && WILLRECEIVE(caller_ptr->p_endpoint, dst_ptr,
			(vir_bytes)&table[i].msg, NULL) &&
			(!(tabent.flags&AMF_NOREPLY) || !(dst_ptr->p_misc_flags&MF_REPLY_PEND))) {
			dst_ptr->p_delivermsg = tabent.msg;
			dst_ptr->p_delivermsg.m_source = caller_ptr->p_endpoint;
			dst_ptr->p_misc_flags |= MF_DELIVERMSG;
			IPC_STATUS_ADD_CALL(dst_ptr, SENDA);
			RTS_UNSET(dst_ptr, RTS_RECEIVING);
#if DEBUG_IPC_HOOK
			hook_ipc_msgrecv(&dst_ptr->p_delivermsg, caller_ptr, dst_ptr);
#endif
		} else if (r == OK) {
			set_sys_bit(priv(dst_ptr)->s_asyn_pending, priv(caller_ptr)->s_id); 
			done = FALSE;
			continue;
		} 

		tabent.result = r;
		tabent.flags |= AMF_DONE;
		if (tabent.flags & AMF_NOTIFY)
			do_notify = TRUE;
		else if (r != OK && (tabent.flags & AMF_NOTIFY_ERR))
			do_notify = TRUE;
		asyn_insert_entry(caller_ptr, table_v, i, &tabent);
		continue;

	asyn_error_in_loop:
		if (tabent.dst != NONE)
			printf("KERNEL senda error %d to %d\n", r, tabent.dst);
		else
			printf("KERNEL senda error %d\n", r);
	}

	if (do_notify) 
		mini_notify(proc_addr(ASYNCM), caller_ptr->p_endpoint);

	if (!done) {
		privp->s_asyntab = (vir_bytes) table;
		privp->s_asynsize = size;
	}

	return OK;
}

static int mini_senda(struct proc *caller_ptr, asynmsg_t *table, size_t size)
{
	struct priv *privp = priv(caller_ptr);
	if (!(privp->s_flags & SYS_PROC)) {
		printf( "mini_senda: warning caller has no privilege structure\n");
		return EPERM;
	}

	return try_deliver_senda(caller_ptr, table, size);
}

static int try_async(struct proc * caller_ptr)
{
	struct priv *privp;
	struct proc *src_ptr;
	sys_map_t *map = &priv(caller_ptr)->s_asyn_pending;

	for (privp = BEG_PRIV_ADDR; privp < END_PRIV_ADDR; ++privp)  {
		if (privp->s_proc_nr == NONE || !get_sys_bit(*map, privp->s_id))
			continue;

		src_ptr = proc_addr(privp->s_proc_nr);
#ifdef CONFIG_SMP
		if (RTS_ISSET(src_ptr, RTS_VMINHIBIT)) {
			src_ptr->p_misc_flags |= MF_SENDA_VM_MISS;
			continue;
		}
#endif
		assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));
		if (try_one(ANY, src_ptr, caller_ptr) == OK)
			return OK;
	}

	return ESRCH;
}

static int try_one(endpoint_t receive_e, struct proc *src_ptr,
    struct proc *dst_ptr)
{
	int r = EAGAIN, done, do_notify;
	unsigned int i;
	size_t size;
	struct priv *privp;
	asynmsg_t tabent;
	vir_bytes table_v;

	privp = priv(src_ptr);
	if (!(privp->s_flags & SYS_PROC)) return EPERM;
	size = privp->s_asynsize;
	table_v = privp->s_asyntab;

	unset_sys_bit(priv(dst_ptr)->s_asyn_pending, privp->s_id);

	if (size == 0) return EAGAIN;
	if (privp->s_asynendpoint != src_ptr->p_endpoint) return EAGAIN;
	if (!may_asynsend_to(src_ptr, proc_nr(dst_ptr))) return ECALLDENIED;

	do_notify = FALSE;
	done = TRUE;

	for (i = 0; i < size; i++) {
		if (asyn_retrieve_entry(src_ptr, table_v, i, &tabent) != OK) {
			r = EFAULT;
			goto asyn_error;
		}

		if (tabent.flags == 0) continue;
		if (tabent.flags & ~(AMF_VALID|AMF_DONE|AMF_NOTIFY|AMF_NOREPLY|AMF_NOTIFY_ERR))
			r = EINVAL;
		else if (!(tabent.flags & AMF_VALID))
			r = EINVAL; 
		else if (tabent.flags & AMF_DONE) continue;
		else
			r = OK;

		done = FALSE;

		if (r != OK)
			goto store_result;

		if (tabent.dst != dst_ptr->p_endpoint) continue;

		if (!CANRECEIVE(receive_e, src_ptr->p_endpoint, dst_ptr,
			table_v + i*sizeof(asynmsg_t) + offsetof(struct asynmsg,msg),
			NULL)) {
			continue;
		}

		if ((tabent.flags & AMF_NOREPLY) && (dst_ptr->p_misc_flags & MF_REPLY_PEND)) 
			continue;

		r = OK;
		dst_ptr->p_delivermsg = tabent.msg;
		dst_ptr->p_delivermsg.m_source = src_ptr->p_endpoint;
		dst_ptr->p_misc_flags |= MF_DELIVERMSG;
#if DEBUG_IPC_HOOK
		hook_ipc_msgrecv(&dst_ptr->p_delivermsg, src_ptr, dst_ptr);
#endif

	store_result:
		tabent.result = r;
		tabent.flags |= AMF_DONE;
		if (tabent.flags & AMF_NOTIFY) do_notify = TRUE;
		else if (r != OK && (tabent.flags & AMF_NOTIFY_ERR)) do_notify = TRUE;
		asyn_insert_entry(src_ptr, table_v, i, &tabent);

		break;
	}

	if (do_notify) 
		mini_notify(proc_addr(ASYNCM), src_ptr->p_endpoint);

	if (done) {
		privp->s_asyntab = -1;
		privp->s_asynsize = 0;
	} else {
		set_sys_bit(priv(dst_ptr)->s_asyn_pending, privp->s_id);
	}

asyn_error:
	return r;
}

int cancel_async(struct proc *src_ptr, struct proc *dst_ptr)
{
	int r = OK, done, do_notify;
	unsigned int i;
	size_t size;
	struct priv *privp;
	asynmsg_t tabent;
	vir_bytes table_v;

	privp = priv(src_ptr);
	if (!(privp->s_flags & SYS_PROC)) return EPERM;
	size = privp->s_asynsize;
	table_v = privp->s_asyntab;

	privp->s_asyntab = -1;
	privp->s_asynsize = 0;
	unset_sys_bit(priv(dst_ptr)->s_asyn_pending, privp->s_id);

	if (size == 0) return EAGAIN;
	if (!may_send_to(src_ptr, proc_nr(dst_ptr))) return ECALLDENIED;

	do_notify = FALSE;
	done = TRUE;

	for (i = 0; i < size; i++) {
		if (asyn_retrieve_entry(src_ptr, table_v, i, &tabent) != OK) {
			r = EFAULT;
			goto asyn_error;
		}

		if (tabent.flags == 0) continue;

		int result = EDEADSRCDST;
		if (tabent.flags & ~(AMF_VALID|AMF_DONE|AMF_NOTIFY|AMF_NOREPLY|AMF_NOTIFY_ERR))
			result = EINVAL;
		else if (!(tabent.flags & AMF_VALID))
			result = EINVAL; 
		else if (tabent.flags & AMF_DONE) continue;
		
		if (tabent.dst != dst_ptr->p_endpoint) {
			done = FALSE;
			continue;
		}

		tabent.result = result;
		tabent.flags |= AMF_DONE;
		if (tabent.flags & AMF_NOTIFY) do_notify = TRUE;
		else if (result != OK && (tabent.flags & AMF_NOTIFY_ERR)) do_notify = TRUE;
		asyn_insert_entry(src_ptr, table_v, i, &tabent);
	}

	if (do_notify) 
		mini_notify(proc_addr(ASYNCM), src_ptr->p_endpoint);

	if (!done) {
		privp->s_asyntab = table_v;
		privp->s_asynsize = size;
	}

asyn_error:
	return r;
}

void enqueue(
  register struct proc *rp
)
{
	int q = rp->p_priority;
	struct proc **rdy_head, **rdy_tail;

	assert(proc_is_runnable(rp));
	assert(q >= 0);

	rdy_head = get_cpu_var(rp->p_cpu, run_q_head);
	rdy_tail = get_cpu_var(rp->p_cpu, run_q_tail);

	if (!rdy_head[q]) {
		rdy_head[q] = rdy_tail[q] = rp;
		rp->p_nextready = NULL;
	} 
	else {
		rdy_tail[q]->p_nextready = rp;		
		rdy_tail[q] = rp;
		rp->p_nextready = NULL;
	}

	if (cpuid == rp->p_cpu) {
		struct proc * p = get_cpulocal_var(proc_ptr);
		assert(p);
		if((p->p_priority > rp->p_priority) && (priv(p)->s_flags & PREEMPTIBLE))
			RTS_SET(p, RTS_PREEMPTED);
	}
#ifdef CONFIG_SMP
	else if (get_cpu_var(rp->p_cpu, cpu_is_idle)) {
		smp_schedule(rp->p_cpu);
	}
#endif
	read_tsc_64(&(get_cpulocal_var(proc_ptr)->p_accounting.enter_queue));

#if DEBUG_SANITYCHECKS
	assert(runqueues_ok_local());
#endif
}

static void enqueue_head(struct proc *rp)
{
	const int q = rp->p_priority;

	struct proc **rdy_head, **rdy_tail;

	assert(proc_ptr_ok(rp));
	assert(proc_is_runnable(rp));
	assert(rp->p_cpu_time_left);
	assert(q >= 0);

	rdy_head = get_cpu_var(rp->p_cpu, run_q_head);
	rdy_tail = get_cpu_var(rp->p_cpu, run_q_tail);

	if (!rdy_head[q]) {
		rdy_head[q] = rdy_tail[q] = rp;
		rp->p_nextready = NULL;
	} else {
		rp->p_nextready = rdy_head[q];
		rdy_head[q] = rp;
	}

	read_tsc_64(&(get_cpulocal_var(proc_ptr->p_accounting.enter_queue)));

	rp->p_accounting.dequeues--;
	rp->p_accounting.preempted++;

#if DEBUG_SANITYCHECKS
	assert(runqueues_ok_local());
#endif
}

void dequeue(struct proc *rp)
{
	int q = rp->p_priority;
	struct proc **xpp;
	struct proc *prev_xp;
	u64_t tsc, tsc_delta;
	struct proc **rdy_tail;

	assert(proc_ptr_ok(rp));
	assert(!proc_is_runnable(rp));
	assert (!iskernelp(rp) || *priv(rp)->s_stack_guard == STACK_GUARD);

	rdy_tail = get_cpu_var(rp->p_cpu, run_q_tail);
	prev_xp = NULL;				
	for (xpp = get_cpu_var_ptr(rp->p_cpu, run_q_head[q]); *xpp;
		xpp = &(*xpp)->p_nextready) {
		if (*xpp == rp) {
			*xpp = (*xpp)->p_nextready;
			if (rp == rdy_tail[q]) {
				rdy_tail[q] = prev_xp;
			}
			break;
		}
		prev_xp = *xpp;
	}
	
	rp->p_accounting.dequeues++;

	if (rp->p_accounting.enter_queue) {
		read_tsc_64(&tsc);
		tsc_delta = tsc - rp->p_accounting.enter_queue;
		rp->p_accounting.time_in_queue = rp->p_accounting.time_in_queue + tsc_delta;
		rp->p_accounting.enter_queue = 0;
	}

	rp->p_dequeued = get_monotonic();

#if DEBUG_SANITYCHECKS
	assert(runqueues_ok_local());
#endif
}

static struct proc * pick_proc(void)
{
	register struct proc *rp;
	struct proc **rdy_head;
	int q;

	rdy_head = get_cpulocal_var(run_q_head);
	for (q=0; q < NR_SCHED_QUEUES; q++) {	
		if(!(rp = rdy_head[q])) {
			TRACE(VF_PICKPROC, printf("cpu %d queue %d empty\n", cpuid, q););
			continue;
		}
		assert(proc_is_runnable(rp));
		if (priv(rp)->s_flags & BILLABLE)	 	
			get_cpulocal_var(bill_ptr) = rp;
		return rp;
	}
	return NULL;
}

struct proc *endpoint_lookup(endpoint_t e)
{
	int n;
	if(!isokendpt(e, &n)) return NULL;
	return proc_addr(n);
}

#if DEBUG_ENABLE_IPC_WARNINGS
int isokendpt_f(const char * file, int line, endpoint_t e, int * p,
	const int fatalflag)
#else
int isokendpt_f(endpoint_t e, int * p, const int fatalflag)
#endif
{
	*p = _ENDPOINT_P(e);
	if(isokprocn(*p) && !isemptyn(*p) && proc_addr(*p)->p_endpoint == e) {
		return 1;
	}
	if(fatalflag) {
		panic("invalid endpoint: %d", e);
	}
	return 0;
}

static void notify_scheduler(struct proc *p)
{
	message m_no_quantum;
	int err;

	assert(!proc_kernel_scheduler(p));

	RTS_SET(p, RTS_NO_QUANTUM);

	m_no_quantum.m_source = p->p_endpoint;
	m_no_quantum.m_type   = SCHEDULING_NO_QUANTUM;
	m_no_quantum.m_krn_lsys_schedule.acnt_queue = cpu_time_2_ms(p->p_accounting.time_in_queue);
	m_no_quantum.m_krn_lsys_schedule.acnt_deqs      = p->p_accounting.dequeues;
	m_no_quantum.m_krn_lsys_schedule.acnt_ipc_sync  = p->p_accounting.ipc_sync;
	m_no_quantum.m_krn_lsys_schedule.acnt_ipc_async = p->p_accounting.ipc_async;
	m_no_quantum.m_krn_lsys_schedule.acnt_preempt   = p->p_accounting.preempted;
	m_no_quantum.m_krn_lsys_schedule.acnt_cpu       = cpuid;
	m_no_quantum.m_krn_lsys_schedule.acnt_cpu_load  = cpu_load();

	reset_proc_accounting(p);

	if ((err = mini_send(p, p->p_scheduler->p_endpoint,
					&m_no_quantum, FROM_KERNEL))) {
		panic("WARNING: Scheduling: mini_send returned %d\n", err);
	}
}

void proc_no_time(struct proc * p)
{
	if (!proc_kernel_scheduler(p) && priv(p)->s_flags & PREEMPTIBLE) {
		notify_scheduler(p);
	}
	else {
		p->p_cpu_time_left = ms_2_cpu_time(p->p_quantum_size_ms);
#if DEBUG_RACE
		RTS_SET(p, RTS_PREEMPTED);
		RTS_UNSET(p, RTS_PREEMPTED);
#endif
	}
}

void reset_proc_accounting(struct proc *p)
{
	p->p_accounting.preempted = 0;
	p->p_accounting.ipc_sync  = 0;
	p->p_accounting.ipc_async = 0;
	p->p_accounting.dequeues  = 0;
	p->p_accounting.time_in_queue = 0;
	p->p_accounting.enter_queue = 0;
}
	
void copr_not_available_handler(void)
{
	struct proc * p;
	struct proc ** local_fpu_owner;

	disable_fpu_exception();

	p = get_cpulocal_var(proc_ptr);

	local_fpu_owner = get_cpulocal_var_ptr(fpu_owner);
	if (*local_fpu_owner != NULL) {
		assert(*local_fpu_owner != p);
		save_local_fpu(*local_fpu_owner, FALSE);
	}

	if (restore_fpu(p) != OK) {
		*local_fpu_owner = NULL;
		cause_sig(proc_nr(p), SIGFPE);
		return;
	}

	*local_fpu_owner = p;
	context_stop(proc_addr(KERNEL));
	restore_user_context(p);
	NOT_REACHABLE;
}

void release_fpu(struct proc * p) {
	struct proc ** fpu_owner_ptr;

	fpu_owner_ptr = get_cpu_var_ptr(p->p_cpu, fpu_owner);

	if (*fpu_owner_ptr == p)
		*fpu_owner_ptr = NULL;
}

void ser_dump_proc(void)
{
	struct proc *pp;

	for (pp= BEG_PROC_ADDR; pp < END_PROC_ADDR; pp++)
	{
		if (isemptyp(pp))
			continue;
		print_proc_recursive(pp);
	}
}