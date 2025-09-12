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

#include <stdio.h>
#include <stddef.h>

static void set_idle_name(char *name, size_t buf_size, int n)
{
    if (name == NULL || buf_size == 0) {
        return;
    }

    if (n > 999) {
        n = 999;
    } else if (n < 0) {
        n = 0;
    }

    snprintf(name, buf_size, "idle%d", n);
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
	for (struct proc *rp = BEG_PROC_ADDR, int i = -NR_TASKS; rp < END_PROC_ADDR; ++rp, ++i) {
		rp->p_rts_flags = RTS_SLOT_FREE;
		rp->p_magic = PMAGIC;
		rp->p_nr = i;
		rp->p_endpoint = _ENDPOINT(0, rp->p_nr);
		rp->p_scheduler = NULL;
		rp->p_priority = 0;
		rp->p_quantum_size_ms = 0;

		arch_proc_reset(rp);
	}
	for (struct priv *sp = BEG_PRIV_ADDR, int i = 0; sp < END_PRIV_ADDR; ++sp, ++i) {
		sp->s_proc_nr = NONE;
		sp->s_id = (sys_id_t) i;
		ppriv_addr[i] = sp;
		sp->s_sig_mgr = NONE;
		sp->s_bak_sig_mgr = NONE;
	}

	idle_priv.s_flags = IDL_F;
	for (int i = 0; i < CONFIG_MAX_CPUS; i++) {
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
#else
	(void)0;
#endif
}

static void idle(void)
{
	struct proc *p;

	struct proc *current_idle_process = get_cpulocal_var_ptr(idle_proc);
	get_cpulocal_var(proc_ptr) = current_idle_process;
	p = current_idle_process;

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

#if !SPROFILE
	halt_cpu();
#else
	if (!sprofiling) {
		halt_cpu();
	} else {
		volatile int *idle_interrupted_flag_ptr = get_cpulocal_var_ptr(idle_interrupted);

		interrupts_enable();
		while (!*idle_interrupted_flag_ptr) {
			arch_pause();
		}
		interrupts_disable();
		*idle_interrupted_flag_ptr = 0;
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

        if (vmrequest == NULL) {
                if (OK != send_sig(VM_PROC_NR, SIGKMEM)) {
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

        if (copy_msg_to_user(&rp->p_delivermsg, (message *) rp->p_delivermsg_vir)) {
                if (rp->p_misc_flags & MF_MSGFAILED) {
                        printf("WARNING wrong user pointer 0x%08lx from process %s / %d\n",
                                rp->p_delivermsg_vir,
                                rp->p_name,
                                rp->p_endpoint);
                        cause_sig(rp->p_nr, SIGSEGV);
                } else {
                        vm_suspend(rp, rp, rp->p_delivermsg_vir,
                                sizeof(message), VMSTYPE_DELIVERMSG, 1);
                        rp->p_misc_flags |= MF_MSGFAILED;
                }
                return;
        }

        rp->p_delivermsg.m_source = NONE;
        rp->p_misc_flags &= ~(MF_DELIVERMSG | MF_MSGFAILED);

        if (!(rp->p_misc_flags & MF_CONTEXT_SET)) {
                rp->p_reg.retreg = OK;
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
		assert (!(p->p_misc_flags & MF_SC_ACTIVE));
		arch_do_syscall(p);
		if ((p->p_misc_flags & MF_SIG_DELAY) &&
				!RTS_ISSET(p, RTS_SENDING)) {
			sig_delay_done(p);
		}
	} else if ((p->p_misc_flags & MF_SC_TRACE) && 
	           (p->p_misc_flags & MF_SC_ACTIVE)) {
		p->p_misc_flags &= ~(MF_SC_TRACE | MF_SC_ACTIVE);
		cause_sig(proc_nr(p), SIGTRAP);
	} else if (p->p_misc_flags & MF_SC_ACTIVE) {
		p->p_misc_flags &= ~MF_SC_ACTIVE;
	}
}

void switch_to_user(void)
{
	struct proc *p;
#ifdef CONFIG_SMP
	int tlb_must_refresh = 0;
#endif
	int needs_reselect;

	do {
		needs_reselect = 0;

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

			do {
				p = pick_proc();
				if (!p) {
					idle();
				}
			} while (!p);
			get_cpulocal_var(proc_ptr) = p;
		}

		assert(p);
		assert(proc_is_runnable(p));

		while (p->p_misc_flags &
			(MF_KCALL_RESUME | MF_DELIVERMSG |
			 MF_SC_DEFER | MF_SC_TRACE | MF_SC_ACTIVE)) {

			assert(proc_is_runnable(p));
			handle_misc_flags(p);

			if (!proc_is_runnable(p)) {
				needs_reselect = 1;
				break;
			}
		}

		if (needs_reselect) {
			continue;
		}

		if (!p->p_cpu_time_left) {
			proc_no_time(p);
		}

		if (!proc_is_runnable(p)) {
			needs_reselect = 1;
			continue;
		}

	} while (needs_reselect);

#ifdef CONFIG_SMP
	if (p->p_misc_flags & MF_FLUSH_TLB && get_cpulocal_var(ptproc) == p)
		tlb_must_refresh = 1;
#endif
	switch_address_space(p);

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

    if (call_nr < 0 || call_nr > IPCNO_HIGHEST || call_nr >= 32) {
#if DEBUG_ENABLE_IPC_WARNINGS
        printf("sys_call: trap %d not allowed (invalid call_nr), caller %d, src_dst %d\n", 
            call_nr, proc_nr(caller_ptr), src_dst_e);
#endif
        return ETRAPDENIED;
    }
    
    callname = ipc_call_names[call_nr];
    if (callname == NULL) {
#if DEBUG_ENABLE_IPC_WARNINGS
        printf("sys_call: trap %d not allowed (callname null), caller %d, src_dst %d\n", 
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

        if (call_nr != RECEIVE) {
            if (!may_send_to(caller_ptr, *src_dst_p)) {
#if DEBUG_ENABLE_IPC_WARNINGS
                printf("sys_call: ipc mask denied %s from %d to %d\n",
                    callname,
                    caller_ptr->p_endpoint, src_dst_e);
#endif
                return ECALLDENIED;
            }
        }
    }

    if (!(priv(caller_ptr)->s_trap_mask & (1 << call_nr))) {
#if DEBUG_ENABLE_IPC_WARNINGS
        printf("sys_call: %s not allowed (trap mask), caller %d, src_dst %d\n", 
            callname, proc_nr(caller_ptr), *src_dst_p);
#endif
        return ETRAPDENIED;
    }

    if (call_nr != SENDREC && call_nr != RECEIVE && iskerneln(*src_dst_p)) {
#if DEBUG_ENABLE_IPC_WARNINGS
        printf("sys_call: trap %s not allowed (kernel dest), caller %d, src_dst %d\n",
             callname, proc_nr(caller_ptr), *src_dst_p); 
#endif
        return ETRAPDENIED;
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
	if (result != OK) {
		return result;
	}

	switch(call_nr) {
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
	}

	return result;
}

static void handle_syscall_trace(struct proc *caller_ptr, reg_t r1, reg_t r2, reg_t r3)
{
    if ((caller_ptr->p_misc_flags & MF_SC_TRACE) && !(caller_ptr->p_misc_flags & MF_SC_DEFER)) {
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
		{
		const size_t senda_max_msg_size = (size_t)16 * (NR_TASKS + NR_PROCS);
		const size_t msg_size = (size_t) r2;

		caller_ptr->p_accounting.ipc_async++;

		if (msg_size > senda_max_msg_size) {
			return EDOM;
		}
		return mini_senda(caller_ptr, (asynmsg_t *) r3, msg_size);
		}
	case MINIX_KERNINFO:
		if (minix_kerninfo_user == NULL) {
			return EBADCALL;
		}
		arch_set_secondary_ipc_return(caller_ptr, minix_kerninfo_user);
		return OK;
	default:
		return EBADCALL;
	}
}

static int check_deadlock_cycle(struct proc *cp, endpoint_t initial_blocked_endpoint)
{
	struct proc *current_proc_ptr;
	int group_size = 1;
	int current_proc_slot;
	endpoint_t next_blocked_endpoint = initial_blocked_endpoint;

	while (next_blocked_endpoint != ANY) {
		okendpt(next_blocked_endpoint, &current_proc_slot);
		current_proc_ptr = proc_addr(current_proc_slot);
		assert(proc_ptr_ok(current_proc_ptr));
		assert(!RTS_ISSET(current_proc_ptr, RTS_SLOT_FREE));
		group_size++;

		endpoint_t blocked_on_id = P_BLOCKEDON(current_proc_ptr);

		if (blocked_on_id == NONE) {
			return 0;
		}

		if (blocked_on_id == cp->p_endpoint) {
			return group_size;
		}
		
		next_blocked_endpoint = blocked_on_id;
	}
	return 0;
}

static int deadlock(int function, struct proc *cp, endpoint_t src_dst_e)
{
	int group_size = check_deadlock_cycle(cp, src_dst_e);

	if (group_size == 2) {
		int src_dst_slot;
		/* Validate the endpoint and get the process slot.
		 * In this context, it's assumed to succeed as src_dst_e is part of a detected cycle.
		 * The return value is intentionally ignored. */
		(void)okendpt(src_dst_e, &src_dst_slot);
		struct proc *xp = proc_addr(src_dst_slot);

		/* This condition is a specific system rule to determine if a 2-process
		 * cycle constitutes an actual deadlock that should be reported.
		 * It checks if xp's RTS_SENDING flag status differs from the state
		 * implied by the 'function' parameter. */
		if ((xp->p_rts_flags ^ (function << 2)) & RTS_SENDING) {
			return 0; /* Not a deadlock for this specific criteria */
		}
	}

#if DEBUG_ENABLE_IPC_WARNINGS
	if (group_size > 0) {
		/* Allocate an array to store process pointers involved in the cycle.
		 * The size is based on the maximum possible number of processes and tasks. */
		struct proc *processes[NR_PROCS + NR_TASKS];
		int i = 0;
		
		processes[i++] = cp; /* Start with the current process */
		
		/* Trace the cycle, using src_dst_e to iterate through blocked-on endpoints. */
		while (src_dst_e != ANY && i < group_size) {
			int current_slot;
			/* Validate and convert the current endpoint to a process slot.
			 * The return value is intentionally ignored. */
			(void)okendpt(src_dst_e, &current_slot);
			struct proc *xp = proc_addr(current_slot);
			processes[i++] = xp;
			src_dst_e = P_BLOCKEDON(xp); /* Move to the next process in the cycle */
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
	return group_size; /* Return the size of the deadlock cycle (0 if none or special case) */
}

static int has_pending(sys_map_t *map, int src_p, int asynm)
{
	if (src_p != ANY) {
		int src_id_candidate = nr_to_id(src_p);

		if (get_sys_bit(*map, src_id_candidate)) {
#ifdef CONFIG_SMP
			struct proc *p = proc_addr(id_to_nr(src_id_candidate));
			if (asynm && RTS_ISSET(p, RTS_VMINHIBIT)) {
				p->p_misc_flags |= MF_SENDA_VM_MISS;
				/* This src_id is inhibited, so it's not returned. */
			} else {
				return src_id_candidate;
			}
#else
			return src_id_candidate;
#endif
		}
		return NULL_PRIV_ID; /* Bit not set or SMP-inhibited case (if CONFIG_SMP) */
	}

	/* src_p == ANY: Search for the first available pending ID */
	sys_id_t found_id = NULL_PRIV_ID;
	int src_id_iterator;

	for (src_id_iterator = 0; src_id_iterator < NR_SYS_PROCS; ) {
		/* Optimization: Skip entire chunks if no bits are set in them. */
		if (src_id_iterator % BITCHUNK_BITS == 0 && (src_id_iterator + BITCHUNK_BITS <= NR_SYS_PROCS)) {
			if (get_sys_bits(*map, src_id_iterator) == 0) {
				src_id_iterator += BITCHUNK_BITS;
				continue;
			}
		}

		/* Check if the current ID has a pending bit. */
		if (!get_sys_bit(*map, src_id_iterator)) {
			src_id_iterator++;
			continue;
		}

		/* A set bit was found at src_id_iterator. Apply CONFIG_SMP specific logic. */
#ifdef CONFIG_SMP
		struct proc *p = proc_addr(id_to_nr(src_id_iterator));
		if (asynm && RTS_ISSET(p, RTS_VMINHIBIT)) {
			p->p_misc_flags |= MF_SENDA_VM_MISS;
			src_id_iterator++; /* This src_id is inhibited; continue searching for the next one. */
			continue;
		}
#endif
		/* This src_id is suitable (bit set and not SMP-inhibited or CONFIG_SMP is not defined). */
		found_id = src_id_iterator;
		break; /* Found the first suitable ID, exit the loop. */
	}

	return found_id;
}

int has_pending_notify(struct proc * caller, int src_p)
{
	if (caller == NULL) {
		return 0;
	}

	if ((void*)priv(caller) == NULL) {
		return 0;
	}

	sys_map_t * map = &priv(caller)->s_notify_pending;
	return has_pending(map, src_p, 0);
}

static const int ASYN_PENDING_SEND_FLAG = 1;

int has_pending_asend(struct proc * caller, int src_p)
{
    if (caller == NULL) {
        return 0;
    }

    struct proc_priv * p_priv = priv(caller);

    if (p_priv == NULL) {
        return 0;
    }

    sys_map_t * map = &(p_priv->s_asyn_pending);

    return has_pending(map, src_p, ASYN_PENDING_SEND_FLAG);
}

void unset_notify_pending(struct proc * caller, int src_p)
{
    if (caller == NULL) {
        return;
    }

    struct proc_private_data *pdata = priv(caller);
    if (pdata == NULL) {
        return;
    }

    sys_map_t * map_ptr = &pdata->s_notify_pending;

    const int max_bits = sizeof(sys_map_t) * CHAR_BIT;
    if (src_p < 0 || src_p >= max_bits) {
        return;
    }

    unset_sys_bit(*map_ptr, src_p);
}

int mini_send(struct proc *caller_ptr, endpoint_t dst_e, message *m_ptr, const int flags)
{
    struct proc *dst_ptr;
    int dst_p;
    int r;

    dst_p = _ENDPOINT_P(dst_e);
    dst_ptr = proc_addr(dst_p);

    if (RTS_ISSET(dst_ptr, RTS_NO_ENDPOINT)) {
        return EDEADSRCDST;
    }

    if (WILLRECEIVE(caller_ptr->p_endpoint, dst_ptr, (vir_bytes)m_ptr, NULL)) {
        if (dst_ptr->p_misc_flags & MF_DELIVERMSG) {
            return EFAULT;
        }

        if (!(flags & FROM_KERNEL)) {
            r = copy_msg_from_user(m_ptr, &dst_ptr->p_delivermsg);
            if (r != OK) {
                return r;
            }
        } else {
            dst_ptr->p_delivermsg = *m_ptr;
            IPC_STATUS_ADD_FLAGS(dst_ptr, IPC_FLG_MSG_FROM_KERNEL);
        }

        dst_ptr->p_delivermsg.m_source = caller_ptr->p_endpoint;
        dst_ptr->p_misc_flags |= MF_DELIVERMSG;

        int call_type = (caller_ptr->p_misc_flags & MF_REPLY_PEND) ? SENDREC
            : (flags & NON_BLOCKING ? SENDNB : SEND);
        IPC_STATUS_ADD_CALL(dst_ptr, call_type);

        if (dst_ptr->p_misc_flags & MF_REPLY_PEND) {
            dst_ptr->p_misc_flags &= ~MF_REPLY_PEND;
        }

        RTS_UNSET(dst_ptr, RTS_RECEIVING);

#if DEBUG_IPC_HOOK
        hook_ipc_msgsend(&dst_ptr->p_delivermsg, caller_ptr, dst_ptr);
        hook_ipc_msgrecv(&dst_ptr->p_delivermsg, caller_ptr, dst_ptr);
#endif
    } else {
        if (flags & NON_BLOCKING) {
            return ENOTREADY;
        }

        if (deadlock(SEND, caller_ptr, dst_e)) {
            return ELOCKED;
        }

        if (caller_ptr->p_q_link != NULL) {
            return EFAULT;
        }

        if (!(flags & FROM_KERNEL)) {
            r = copy_msg_from_user(m_ptr, &caller_ptr->p_sendmsg);
            if (r != OK) {
                return r;
            }
        } else {
            caller_ptr->p_sendmsg = *m_ptr;
            caller_ptr->p_misc_flags |= MF_SENDING_FROM_KERNEL;
        }

        RTS_SET(caller_ptr, RTS_SENDING);
        caller_ptr->p_sendto_e = dst_e;

        struct proc **xpp = &dst_ptr->p_caller_q;
        while (*xpp) {
            xpp = &(*xpp)->p_q_link;
        }
        *xpp = caller_ptr;

#if DEBUG_IPC_HOOK
        hook_ipc_msgsend(&caller_ptr->p_sendmsg, caller_ptr, dst_ptr);
#endif
    }

    return OK;
}

static int check_pending_notifications(struct proc *caller_ptr, int src_p, endpoint_t src_e)
{
	int src_id = has_pending_notify(caller_ptr, src_p);

	if (src_id == NULL_PRIV_ID) {
		return 0;
	}

	int src_proc_nr = id_to_nr(src_id);

	struct proc *sender_proc = proc_addr(src_proc_nr);
	if (sender_proc == NULL) {
		return 0;
	}
	endpoint_t sender_e = sender_proc->p_endpoint;

	if (!CANRECEIVE(src_e, sender_e, caller_ptr, 0, &m_notify_buff)) {
		return 0;
	}

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
    if (caller_ptr == NULL) {
        return 0;
    }

    if (has_pending_asend(caller_ptr, src_p) == NULL_PRIV_ID) {
        return 0;
    }

    int result_code;
    if (src_p != ANY) {
        result_code = try_one(src_e, proc_addr(src_p), caller_ptr);
    } else {
        result_code = try_async(caller_ptr);
    }

    if (result_code == OK) {
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
			assert(!RTS_ISSET(sender, RTS_SLOT_FREE));
			assert(!RTS_ISSET(sender, RTS_NO_ENDPOINT));

			assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));
			caller_ptr->p_delivermsg = sender->p_sendmsg;
			
            // Upon successful message delivery, remove the sender from the queue
            // and indicate success. Assuming 'p_q_next' is the pointer to the next element in the queue.
            *xpp = sender->p_q_next;
			return 1;
		} else {
            // Sender cannot receive, move to the next sender in the queue.
            // Assuming 'p_q_next' is the pointer to the next element in the queue.
            xpp = &sender->p_q_next;
		}
	}
	return 0; // No suitable sender found in the queue
}