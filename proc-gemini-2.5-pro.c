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
    const int MAX_IDLE_NUM = 999;
    int number = n;
    char *p = name;
    int divisor;
    int digit_printed = 0;

    if (number < 0) {
        number = 0;
    } else if (number > MAX_IDLE_NUM) {
        number = MAX_IDLE_NUM;
    }

    *p++ = 'i';
    *p++ = 'd';
    *p++ = 'l';
    *p++ = 'e';

    for (divisor = 100; divisor > 0; divisor /= 10) {
        const int digit = number / divisor;

        if (digit != 0 || digit_printed || divisor == 1) {
            *p++ = '0' + digit;
            digit_printed = 1;
        }
        number %= divisor;
    }

    *p = '\0';
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

static void init_proc_slots(void)
{
	const int num_procs = END_PROC_ADDR - BEG_PROC_ADDR;

	for (int i = 0; i < num_procs; ++i) {
		struct proc *rp = &BEG_PROC_ADDR[i];
		const int proc_nr = i - NR_TASKS;

		rp->p_rts_flags = RTS_SLOT_FREE;
		rp->p_magic = PMAGIC;
		rp->p_nr = proc_nr;
		rp->p_endpoint = _ENDPOINT(0, proc_nr);
		rp->p_scheduler = NULL;
		rp->p_priority = 0;
		rp->p_quantum_size_ms = 0;

		arch_proc_reset(rp);
	}
}

static void init_priv_slots(void)
{
	const int num_privs = END_PRIV_ADDR - BEG_PRIV_ADDR;

	for (int i = 0; i < num_privs; ++i) {
		struct priv *sp = &BEG_PRIV_ADDR[i];

		sp->s_proc_nr = NONE;
		sp->s_id = (sys_id_t) i;
		ppriv_addr[i] = sp;
		sp->s_sig_mgr = NONE;
		sp->s_bak_sig_mgr = NONE;
	}
}

static void init_idle_procs(void)
{
	idle_priv.s_flags = IDL_F;
	for (int i = 0; i < CONFIG_MAX_CPUS; i++) {
		struct proc *ip = get_cpu_var_ptr(i, idle_proc);

		ip->p_endpoint = IDLE;
		ip->p_priv = &idle_priv;
		ip->p_rts_flags |= RTS_PROC_STOP;
		set_idle_name(ip->p_name, i);
	}
}

void proc_init(void)
{
	init_proc_slots();
	init_priv_slots();
	init_idle_procs();
}

#ifdef CONFIG_SMP
static void switch_address_space_idle(void)
{
    switch_address_space(proc_addr(VM_PROC_NR));
}
#else
static inline void switch_address_space_idle(void)
{
    /* This is a no-op in non-SMP configurations. */
}
#endif

static void idle(void)
{
	struct proc *p;

	p = get_cpulocal_var_ptr(idle_proc);
	get_cpulocal_var(proc_ptr) = p;

	if ((priv(p)->s_flags & BILLABLE) != 0) {
		get_cpulocal_var(bill_ptr) = p;
	}

	switch_address_space_idle();

#ifdef CONFIG_SMP
	get_cpulocal_var(cpu_is_idle) = 1;
	if (cpuid == bsp_cpu_id) {
		restart_local_timer();
	} else {
		stop_local_timer();
	}
#else
	restart_local_timer();
#endif

	context_stop(proc_addr(KERNEL));

#if SPROFILE
	if (sprofiling) {
		volatile int *idle_interrupted_flag =
		    get_cpulocal_var_ptr(idle_interrupted);

		interrupts_enable();
		while (*idle_interrupted_flag == 0) {
			arch_pause();
		}
		interrupts_disable();
		*idle_interrupted_flag = 0;
	} else
#endif
	{
		halt_cpu();
	}
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

        if (vmrequest == NULL) {
                if (send_sig(VM_PROC_NR, SIGKMEM) != OK) {
                        panic("send_sig failed");
                }
        }

        vmrequest = caller;
}

static void handle_delivery_failure(struct proc *rp)
{
    if (rp->p_misc_flags & MF_MSGFAILED) {
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
}

static void handle_delivery_success(struct proc *rp)
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

    if (copy_msg_to_user(&rp->p_delivermsg, (message *)rp->p_delivermsg_vir)) {
        handle_delivery_failure(rp);
    } else {
        handle_delivery_success(rp);
    }
}

static void handle_misc_flags(struct proc *p)
{
	if (p->p_misc_flags & MF_KCALL_RESUME) {
		kernel_call_resume(p);
	} else if (p->p_misc_flags & MF_DELIVERMSG) {
		TRACE(VF_SCHEDULING, printf("delivering to %s / %d\n",
			p->p_name, p->p_endpoint););
		delivermsg(p);
	} else if (p->p_misc_flags & MF_SC_DEFER) {
		assert(!(p->p_misc_flags & MF_SC_ACTIVE));
		arch_do_syscall(p);
		if ((p->p_misc_flags & MF_SIG_DELAY) && !RTS_ISSET(p, RTS_SENDING)) {
			sig_delay_done(p);
		}
	} else if (p->p_misc_flags & MF_SC_ACTIVE) {
		if (p->p_misc_flags & MF_SC_TRACE) {
			p->p_misc_flags &= ~MF_SC_TRACE;
			cause_sig(proc_nr(p), SIGTRAP);
		}
		p->p_misc_flags &= ~MF_SC_ACTIVE;
	}
}

void switch_to_user(void)
{
	struct proc *p;
#ifdef CONFIG_SMP
	int tlb_must_refresh = 0;
#endif

	while (1) {
		int is_still_runnable = 1;
		p = get_cpulocal_var(proc_ptr);

		if (!proc_is_runnable(p)) {
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

			while (!(p = pick_proc())) {
				idle();
			}

			get_cpulocal_var(proc_ptr) = p;

#ifdef CONFIG_SMP
			if ((p->p_misc_flags & MF_FLUSH_TLB) && (get_cpulocal_var(ptproc) == p)) {
				tlb_must_refresh = 1;
			}
#endif
			switch_address_space(p);
		}

		assert(p);
		assert(proc_is_runnable(p));

		while (p->p_misc_flags &
			(MF_KCALL_RESUME | MF_DELIVERMSG |
			 MF_SC_DEFER | MF_SC_TRACE | MF_SC_ACTIVE)) {
			assert(proc_is_runnable(p));
			handle_misc_flags(p);

			if (!proc_is_runnable(p)) {
				is_still_runnable = 0;
				break;
			}
		}

		if (!is_still_runnable) {
			continue;
		}

		if (!p->p_cpu_time_left) {
			proc_no_time(p);
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
		if (tlb_must_refresh) {
			refresh_tlb();
		}
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
	const char *callname;

	if (call_nr < 0 || call_nr > IPCNO_HIGHEST || call_nr >= 32
	    || !(callname = ipc_call_names[call_nr])) {
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

	if (!(priv(caller_ptr)->s_trap_mask & (1 << call_nr))) {
#if DEBUG_ENABLE_IPC_WARNINGS
		printf("sys_call: %s not allowed, caller %d, src_dst %d\n",
		    callname, proc_nr(caller_ptr), *src_dst_p);
#endif
		return ETRAPDENIED;
	}

	if (iskerneln(*src_dst_p) && call_nr != SENDREC && call_nr != RECEIVE) {
#if DEBUG_ENABLE_IPC_WARNINGS
		printf("sys_call: trap %s not allowed, caller %d, src_dst %d\n",
		     callname, proc_nr(caller_ptr), src_dst_e);
#endif
		return ETRAPDENIED;
	}

	return OK;
}

static int do_sync_ipc(struct proc *caller_ptr, int call_nr,
			endpoint_t src_dst_e, message *m_ptr)
{
	int result;
	int src_dst_p;

	assert(call_nr != SENDA);

	result = validate_ipc_call(caller_ptr, call_nr, src_dst_e, &src_dst_p);
	if (result != OK) {
		return result;
	}

	switch (call_nr) {
	case SENDREC:
		caller_ptr->p_misc_flags |= MF_REPLY_PEND;
		result = mini_send(caller_ptr, src_dst_e, m_ptr, 0);
		if (result == OK) {
			result = mini_receive(caller_ptr, src_dst_e, m_ptr, 0);
		}
		break;
	case RECEIVE:
		caller_ptr->p_misc_flags &= ~MF_REPLY_PEND;
		IPC_STATUS_CLEAR(caller_ptr);
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
		break;
	}

	return result;
}

static void handle_syscall_trace(struct proc *caller_ptr, reg_t r1, reg_t r2, reg_t r3)
{
	if (!caller_ptr) {
		return;
	}

	if ((caller_ptr->p_misc_flags & (MF_SC_TRACE | MF_SC_DEFER)) == MF_SC_TRACE) {
		caller_ptr->p_misc_flags &= ~MF_SC_TRACE;
		caller_ptr->p_misc_flags |= MF_SC_DEFER;

		caller_ptr->p_defer.r1 = r1;
		caller_ptr->p_defer.r2 = r2;
		caller_ptr->p_defer.r3 = r3;

		cause_sig(proc_nr(caller_ptr), SIGTRAP);
	} else {
		caller_ptr->p_misc_flags &= ~MF_SC_DEFER;
		assert(!(caller_ptr->p_misc_flags & MF_SC_ACTIVE));
		caller_ptr->p_misc_flags |= MF_SC_ACTIVE;
	}
}

int do_ipc(reg_t r1, reg_t r2, reg_t r3)
{
	struct proc *const caller_ptr = get_cpulocal_var(proc_ptr);
	const int call_nr = (int) r1;

	assert(!RTS_ISSET(caller_ptr, RTS_SLOT_FREE));

	kbill_ipc = caller_ptr;

	if (caller_ptr->p_misc_flags & (MF_SC_TRACE | MF_SC_DEFER)) {
		const int prev_result = caller_ptr->p_reg.retreg;
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
	{
		static const size_t MAX_ASYNC_MSG_SIZE = 16 * (NR_TASKS + NR_PROCS);
		const size_t msg_size = (size_t) r2;

		caller_ptr->p_accounting.ipc_async++;

		if (msg_size > MAX_ASYNC_MSG_SIZE) {
			return EDOM;
		}
		return mini_senda(caller_ptr, (asynmsg_t *) r3, msg_size);
	}
	case MINIX_KERNINFO:
		if (minix_kerninfo_user) {
			arch_set_secondary_ipc_return(caller_ptr, minix_kerninfo_user);
			return OK;
		}
		return EBADCALL;
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
		if (okendpt(src_dst_e, &src_dst_slot) != OK) {
			return 0;
		}

		xp = proc_addr(src_dst_slot);
		assert(proc_ptr_ok(xp));
		assert(!RTS_ISSET(xp, RTS_SLOT_FREE));

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

#if DEBUG_ENABLE_IPC_WARNINGS
static void print_deadlock_report(int group_size, struct proc *cp,
	endpoint_t src_dst_e)
{
	struct proc *processes[NR_PROCS + NR_TASKS];
	int count = 0;
	int i;

	processes[count++] = cp;
	while (src_dst_e != ANY && count < group_size) {
		int slot;
		struct proc *p;

		if (okendpt(src_dst_e, &slot) != OK) {
			break;
		}
		p = proc_addr(slot);
		if (!p) {
			break;
		}
		processes[count++] = p;
		src_dst_e = P_BLOCKEDON(p);
	}

	printf("deadlock between these processes:\n");
	for (i = 0; i < count; i++) {
		printf(" %10s ", processes[i]->p_name);
	}
	printf("\n\n");

	for (i = 0; i < count; i++) {
		print_proc(processes[i]);
		proc_stacktrace(processes[i]);
	}
}
#endif

static int deadlock(int function, struct proc *cp, endpoint_t src_dst_e)
{
	int group_size = check_deadlock_cycle(cp, src_dst_e);

	if (group_size == 2) {
		int src_dst_slot;
		if (okendpt(src_dst_e, &src_dst_slot) == OK) {
			struct proc *xp = proc_addr(src_dst_slot);
			if (xp) {
				const int xp_is_sending = (xp->p_rts_flags & RTS_SENDING) != 0;
				const int op_is_sending = ((function << 2) & RTS_SENDING) != 0;

				if (xp_is_sending != op_is_sending) {
					return 0;
				}
			}
		}
	}

#if DEBUG_ENABLE_IPC_WARNINGS
	if (group_size > 0) {
		print_deadlock_report(group_size, cp, src_dst_e);
	}
#endif
	return group_size;
}

static int has_pending(sys_map_t *map, int src_p, int asynm)
{
	if (src_p != ANY) {
		int src_id = nr_to_id(src_p);
		if (get_sys_bit(*map, src_id)) {
#ifdef CONFIG_SMP
			struct proc *p = proc_addr(id_to_nr(src_id));
			if (asynm && RTS_ISSET(p, RTS_VMINHIBIT)) {
				p->p_misc_flags |= MF_SENDA_VM_MISS;
				return NULL_PRIV_ID;
			}
#endif
			return src_id;
		}
		return NULL_PRIV_ID;
	}

	for (int i = 0; i < NR_SYS_PROCS; i += BITCHUNK_BITS) {
		if (get_sys_bits(*map, i) == 0) {
			continue;
		}

		for (int src_id = i;
		     src_id < i + BITCHUNK_BITS && src_id < NR_SYS_PROCS;
		     src_id++) {
			if (get_sys_bit(*map, src_id)) {
#ifdef CONFIG_SMP
				struct proc *p = proc_addr(id_to_nr(src_id));
				if (asynm && RTS_ISSET(p, RTS_VMINHIBIT)) {
					p->p_misc_flags |= MF_SENDA_VM_MISS;
					continue;
				}
#endif
				return src_id;
			}
		}
	}

	return NULL_PRIV_ID;
}

int has_pending_notify(const struct proc *caller, int src_p)
{
    if (!caller) {
        return 0;
    }
    
    sys_map_t *map = &priv(caller)->s_notify_pending;
    return has_pending(map, src_p, 0);
}

int has_pending_asend(struct proc * caller, int src_p)
{
	if (!caller || !priv(caller)) {
		return 0;
	}
	return has_pending(&priv(caller)->s_asyn_pending, src_p, 1);
}

void unset_notify_pending(struct proc *caller, int src_p)
{
    if (caller) {
        unset_sys_bit(priv(caller)->s_notify_pending, src_p);
    }
}

int mini_send(struct proc *caller_ptr, endpoint_t dst_e,
              message *m_ptr, const int flags)
{
    const int dst_p = _ENDPOINT_P(dst_e);
    struct proc * const dst_ptr = proc_addr(dst_p);

    if (RTS_ISSET(dst_ptr, RTS_NO_ENDPOINT)) {
        return EDEADSRCDST;
    }

    /* Check if the destination is ready to receive. If so, deliver immediately. */
    if (WILLRECEIVE(caller_ptr->p_endpoint, dst_ptr, (vir_bytes)m_ptr, NULL)) {
        assert(!(dst_ptr->p_misc_flags & MF_DELIVERMSG));

        if (!(flags & FROM_KERNEL)) {
            if (copy_msg_from_user(m_ptr, &dst_ptr->p_delivermsg)) {
                return EFAULT;
            }
        } else {
            dst_ptr->p_delivermsg = *m_ptr;
            IPC_STATUS_ADD_FLAGS(dst_ptr, IPC_FLG_MSG_FROM_KERNEL);
        }

        dst_ptr->p_delivermsg.m_source = caller_ptr->p_endpoint;
        dst_ptr->p_misc_flags |= MF_DELIVERMSG;

        int call;
        if (caller_ptr->p_misc_flags & MF_REPLY_PEND) {
            call = SENDREC;
        } else if (flags & NON_BLOCKING) {
            call = SENDNB;
        } else {
            call = SEND;
        }
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

    /* Destination is not ready. Block the sender if allowed. */
    if (flags & NON_BLOCKING) {
        return ENOTREADY;
    }

    if (deadlock(SEND, caller_ptr, dst_e)) {
        return ELOCKED;
    }

    /* Copy the message to the sender's send buffer to be sent later. */
    if (!(flags & FROM_KERNEL)) {
        if (copy_msg_from_user(m_ptr, &caller_ptr->p_sendmsg)) {
            return EFAULT;
        }
    } else {
        caller_ptr->p_sendmsg = *m_ptr;
        caller_ptr->p_misc_flags |= MF_SENDING_FROM_KERNEL;
    }

    RTS_SET(caller_ptr, RTS_SENDING);
    caller_ptr->p_sendto_e = dst_e;

    /* Add the sender to the destination's queue of waiting senders. */
    assert(caller_ptr->p_q_link == NULL);
    struct proc **xpp = &dst_ptr->p_caller_q;
    while (*xpp) {
        xpp = &(*xpp)->p_q_link;
    }
    *xpp = caller_ptr;

#if DEBUG_IPC_HOOK
    hook_ipc_msgsend(&caller_ptr->p_sendmsg, caller_ptr, dst_ptr);
#endif

    return OK;
}

static int check_pending_notifications(struct proc *caller_ptr, int src_p, endpoint_t src_e)
{
	const int src_id = has_pending_notify(caller_ptr, src_p);
	if (src_id == NULL_PRIV_ID) {
		return 0;
	}

	const int src_proc_nr = id_to_nr(src_id);
	if (src_proc_nr == NONE) {
#if DEBUG_ENABLE_IPC_WARNINGS
		printf("check_pending_notifications: received notify from invalid src_id %d\n", src_id);
#endif
		return 0;
	}

	const endpoint_t sender_e = proc_addr(src_proc_nr)->p_endpoint;
	if (!CANRECEIVE(src_e, sender_e, caller_ptr, 0, &m_notify_buff)) {
		return 0;
	}

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
	if (has_pending_asend(caller_ptr, src_p) == NULL_PRIV_ID) {
		return 0;
	}

	int r = (src_p != ANY) ? 
		try_one(src_e, proc_addr(src_p), caller_ptr) : 
		try_async(caller_ptr);

	if (r != OK) {
		return 0;
	}

	IPC_STATUS_ADD_CALL(caller_ptr, SENDA);
	return 1;
}

static int check_caller_queue(struct proc *caller_ptr, const endpoint_t src_e)
{
    struct proc **queue_link_ptr = &caller_ptr->p_caller_q;

    while (*queue_link_ptr) {
        struct proc *sender = *queue_link_ptr;
        const endpoint_t sender_e = sender->p_endpoint;

        if (CANRECEIVE(src_e, sender_e, caller_ptr, 0, &sender->p_sendmsg)) {
            assert(!RTS_ISSET(sender, RTS_SLOT_FREE));
            assert(!RTS_ISSET(sender, RTS_NO_ENDPOINT));
            assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));

            /* Dequeue the sender from the caller's queue. */
            *queue_link_ptr = sender->p_nextsender;

            /* Prepare the message for delivery. */
            caller_ptr->p_delivermsg = sender->p_sendmsg;
            caller_ptr->p_delivermsg.m_source = sender->p_endpoint;
            caller_ptr->p_misc_flags |= MF_DELIVERMSG;

            return 1; /* Indicate a message was found and enqueued. */
        }

        /* This sender is not a match, advance to the next one. */
        queue_link_ptr = &sender->p_nextsender;
    }

    return 0; /* No suitable sender found. */
}