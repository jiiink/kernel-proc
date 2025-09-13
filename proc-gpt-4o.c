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
#include <string.h>
#include <limits.h>

#define MAX_IDLE_NAME_LENGTH 8

static void set_idle_name(char *name, int n) {
    if (name == NULL) {
        return;
    }

    if (n < 0) {
        n = 0;
    } else if (n > 999) {
        n = 999;
    }

    snprintf(name, MAX_IDLE_NAME_LENGTH, "idle%d", n);
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

void proc_init(void) {
	struct proc *rp;
	struct priv *sp;
	int i;

	for (rp = BEG_PROC_ADDR; rp < END_PROC_ADDR; ++rp) {
		rp->p_rts_flags = RTS_SLOT_FREE;
		rp->p_magic = PMAGIC;
		rp->p_nr = rp - BEG_PROC_ADDR - NR_TASKS;
		rp->p_endpoint = _ENDPOINT(0, rp->p_nr);
		rp->p_scheduler = NULL;
		rp->p_priority = 0;
		rp->p_quantum_size_ms = 0;

		arch_proc_reset(rp);
	}

	for (sp = BEG_PRIV_ADDR, i = 0; sp < END_PRIV_ADDR; ++sp, ++i) {
		sp->s_proc_nr = NONE;
		sp->s_id = (sys_id_t)i;
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
#ifndef CONFIG_SMP
    return;
#endif
    switch_address_space(proc_addr(VM_PROC_NR));
}

static void idle(void)
{
    struct proc *p = get_cpulocal_var(proc_ptr) = get_cpulocal_var_ptr(idle_proc);

    if (priv(p)->s_flags & BILLABLE) {
        get_cpulocal_var(bill_ptr) = p;
    }

    switch_address_space_idle();

#ifdef CONFIG_SMP
    get_cpulocal_var(cpu_is_idle) = 1;
    if (cpuid != bsp_cpu_id) {
        stop_local_timer();
    } else {
#endif
        restart_local_timer();
#ifdef CONFIG_SMP
    }
#endif

    context_stop(proc_addr(KERNEL));

#if !SPROFILE
    halt_cpu();
#else
    if (!sprofiling) {
        halt_cpu();
    } else {
        volatile int *v = get_cpulocal_var_ptr(idle_interrupted);
        interrupts_enable();
        while (!*v) {
            arch_pause();
        }
        interrupts_disable();
        *v = 0;
    }
#endif
}

void vm_suspend(struct proc *caller, const struct proc *target,
                 const vir_bytes linaddr, const vir_bytes len, const int type,
                 const int writeflag) {
    assert(caller != NULL && target != NULL);
    assert(!RTS_ISSET(caller, RTS_VMREQUEST));
    assert(!RTS_ISSET(target, RTS_VMREQUEST));

    RTS_SET(caller, RTS_VMREQUEST);

    caller->p_vmrequest.req_type = VMPTYPE_CHECK;
    caller->p_vmrequest.target = target->p_endpoint;
    caller->p_vmrequest.params.check.start = linaddr;
    caller->p_vmrequest.params.check.length = len;
    caller->p_vmrequest.params.check.writeflag = writeflag;
    caller->p_vmrequest.type = type;

    if (!caller->p_vmrequest.nextrequestor) {
        caller->p_vmrequest.nextrequestor = vmrequest;
        if (send_sig(VM_PROC_NR, SIGKMEM) != OK) {
            panic("send_sig failed");
        }
    }
    vmrequest = caller;
}

#include <stdio.h>
#include <assert.h>

static void delivermsg(struct proc *rp) {
    if (!rp || RTS_ISSET(rp, RTS_VMREQUEST) || !(rp->p_misc_flags & MF_DELIVERMSG) || rp->p_delivermsg.m_source == NONE) {
        return;
    }

    if (copy_msg_to_user(&rp->p_delivermsg, (message *) rp->p_delivermsg_vir)) {
        if (rp->p_misc_flags & MF_MSGFAILED) {
            printf("WARNING: wrong user pointer 0x%08lx from process %s / %d\n",
                   rp->p_delivermsg_vir, rp->p_name, rp->p_endpoint);
            cause_sig(rp->p_nr, SIGSEGV);
        } else {
            vm_suspend(rp, rp, rp->p_delivermsg_vir, sizeof(message), VMSTYPE_DELIVERMSG, 1);
            rp->p_misc_flags |= MF_MSGFAILED;
        }
    } else {
        rp->p_delivermsg.m_source = NONE;
        rp->p_misc_flags &= ~(MF_DELIVERMSG | MF_MSGFAILED);

        if (!(rp->p_misc_flags & MF_CONTEXT_SET)) {
            rp->p_reg.retreg = OK;
        }
    }
}

#include <stdbool.h>

static void handle_misc_flags(struct proc *p) {
    bool is_kcall_resume = p->p_misc_flags & MF_KCALL_RESUME;
    bool is_delivermsg = p->p_misc_flags & MF_DELIVERMSG;
    bool is_sc_defer = p->p_misc_flags & MF_SC_DEFER;
    bool is_sc_trace = p->p_misc_flags & MF_SC_TRACE;
    bool is_sc_active = p->p_misc_flags & MF_SC_ACTIVE;

    if (is_kcall_resume) {
        kernel_call_resume(p);
    } else if (is_delivermsg) {
        TRACE(VF_SCHEDULING, printf("delivering to %s / %d\n", p->p_name, p->p_endpoint););
        delivermsg(p);
    } else if (is_sc_defer) {
        assert(!is_sc_active);
        arch_do_syscall(p);
        if ((p->p_misc_flags & MF_SIG_DELAY) && !RTS_ISSET(p, RTS_SENDING)) {
            sig_delay_done(p);
        }
    } else if (is_sc_trace && is_sc_active) {
        p->p_misc_flags &= ~(MF_SC_TRACE | MF_SC_ACTIVE);
        cause_sig(proc_nr(p), SIGTRAP);
    } else if (is_sc_active) {
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
        p = get_cpulocal_var(proc_ptr);

        if (!proc_is_runnable(p)) {
            if (proc_is_preempted(p)) {
                p->p_rts_flags &= ~RTS_PREEMPTED;
                if (proc_is_runnable(p)) {
                    enqueue(p->p_cpu_time_left ? p : enqueue_head(p));
                }
            }

            while (!(p = pick_proc())) {
                idle();
            }
            get_cpulocal_var(proc_ptr) = p;
        }

#ifdef CONFIG_SMP
        if ((p->p_misc_flags & MF_FLUSH_TLB) && (get_cpulocal_var(ptproc) == p)) {
            tlb_must_refresh = 1;
        }
#endif

        switch_address_space(p);

        while (p->p_misc_flags & (MF_KCALL_RESUME | MF_DELIVERMSG |
                                  MF_SC_DEFER | MF_SC_TRACE | MF_SC_ACTIVE)) {
            handle_misc_flags(p);
            if (!proc_is_runnable(p)) {
                break;
            }
        }

        if (!proc_is_runnable(p)) {
            continue;
        }

        if (!p->p_cpu_time_left) {
            proc_no_time(p);
        }

        if (!proc_is_runnable(p)) {
            continue;
        }

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
        if ((p->p_misc_flags & MF_FLUSH_TLB) && tlb_must_refresh) {
            refresh_tlb();
        }
        p->p_misc_flags &= ~MF_FLUSH_TLB;
#endif

        restart_local_timer();
        restore_user_context(p);
        NOT_REACHABLE;
    }
}

static int validate_ipc_call(struct proc *caller_ptr, int call_nr, endpoint_t src_dst_e, int *src_dst_p) {
    if (call_nr < 0 || call_nr > IPCNO_HIGHEST || call_nr >= 32 || !ipc_call_names[call_nr]) {
#if DEBUG_ENABLE_IPC_WARNINGS
        printf("sys_call: trap %d not allowed, caller %d, src_dst %d\n", call_nr, proc_nr(caller_ptr), src_dst_e);
#endif
        return ETRAPDENIED;
    }

    const char *callname = ipc_call_names[call_nr];

    if (src_dst_e == ANY) {
        if (call_nr != RECEIVE) return EINVAL;
        *src_dst_p = (int)src_dst_e;
    } else {
        if (!isokendpt(src_dst_e, src_dst_p)) return EDEADSRCDST;
        if (call_nr != RECEIVE && !may_send_to(caller_ptr, *src_dst_p)) {
#if DEBUG_ENABLE_IPC_WARNINGS
            printf("sys_call: ipc mask denied %s from %d to %d\n", callname, caller_ptr->p_endpoint, src_dst_e);
#endif
            return ECALLDENIED;
        }
    }

    if (!(priv(caller_ptr)->s_trap_mask & (1 << call_nr))) {
#if DEBUG_ENABLE_IPC_WARNINGS
        printf("sys_call: %s not allowed, caller %d, src_dst %d\n", callname, proc_nr(caller_ptr), *src_dst_p);
#endif
        return ETRAPDENIED;
    }

    if (call_nr != SENDREC && call_nr != RECEIVE && iskerneln(*src_dst_p)) {
#if DEBUG_ENABLE_IPC_WARNINGS
        printf("sys_call: trap %s not allowed, caller %d, src_dst %d\n", callname, proc_nr(caller_ptr), src_dst_e);
#endif
        return ETRAPDENIED;
    }

    return OK;
}

int do_sync_ipc(struct proc *caller_ptr, int call_nr, endpoint_t src_dst_e, message *m_ptr) {
    int result, src_dst_p;

    assert(call_nr != SENDA);

    if ((result = validate_ipc_call(caller_ptr, call_nr, src_dst_e, &src_dst_p)) != OK) {
        return result;
    }

    if (call_nr == SENDREC) {
        caller_ptr->p_misc_flags |= MF_REPLY_PEND;
        result = mini_send(caller_ptr, src_dst_e, m_ptr, 0);
        if (result == OK) {
            result = mini_receive(caller_ptr, src_dst_e, m_ptr, 0);
        } else {
            caller_ptr->p_misc_flags &= ~MF_REPLY_PEND;
        }
    } else if (call_nr == RECEIVE) {
        caller_ptr->p_misc_flags &= ~MF_REPLY_PEND;
        IPC_STATUS_CLEAR(caller_ptr);
        result = mini_receive(caller_ptr, src_dst_e, m_ptr, 0);
    } else if (call_nr == SEND) {
        result = mini_send(caller_ptr, src_dst_e, m_ptr, 0);
    } else if (call_nr == NOTIFY) {
        result = mini_notify(caller_ptr, src_dst_e);
    } else if (call_nr == SENDNB) {
        result = mini_send(caller_ptr, src_dst_e, m_ptr, NON_BLOCKING);
    } else {
        result = EBADCALL;
    }

    return result;
}

static void handle_syscall_trace(struct proc *caller_ptr, reg_t r1, reg_t r2, reg_t r3)
{
	if ((caller_ptr->p_misc_flags & MF_SC_TRACE) && !(caller_ptr->p_misc_flags & MF_SC_DEFER)) {
		caller_ptr->p_misc_flags = (caller_ptr->p_misc_flags & ~MF_SC_TRACE) | MF_SC_DEFER;
		caller_ptr->p_defer.r1 = r1;
		caller_ptr->p_defer.r2 = r2;
		caller_ptr->p_defer.r3 = r3;
		cause_sig(proc_nr(caller_ptr), SIGTRAP);
	} else {
		caller_ptr->p_misc_flags = (caller_ptr->p_misc_flags & ~MF_SC_DEFER) | MF_SC_ACTIVE;
		assert(!(caller_ptr->p_misc_flags & MF_SC_ACTIVE));
	}
}

int do_ipc(reg_t r1, reg_t r2, reg_t r3) {
    struct proc *const caller_ptr = get_cpulocal_var(proc_ptr);
    int call_nr = (int)r1;
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
        panic("sys_call: MF_DELIVERMSG on for %s / %d\n", caller_ptr->p_name, caller_ptr->p_endpoint);
    }

    switch (call_nr) {
        case SENDREC:
        case SEND:
        case RECEIVE:
        case NOTIFY:
        case SENDNB:
            caller_ptr->p_accounting.ipc_sync++;
            return do_sync_ipc(caller_ptr, call_nr, (endpoint_t)r2, (message *)r3);
        case SENDA: {
            size_t msg_size = (size_t)r2;

            if (msg_size > 16 * (NR_TASKS + NR_PROCS)) {
                return EDOM;
            }

            caller_ptr->p_accounting.ipc_async++;
            return mini_senda(caller_ptr, (asynmsg_t *)r3, msg_size);
        }
        case MINIX_KERNINFO:
            if (!minix_kerninfo_user) {
                return EBADCALL;
            }
            arch_set_secondary_ipc_return(caller_ptr, minix_kerninfo_user);
            return OK;
        default:
            return EBADCALL;
    }
}

static int check_deadlock_cycle(struct proc *cp, endpoint_t src_dst_e) {
    struct proc *xp;
    int group_size = 1;
    int src_dst_slot;

    while (src_dst_e != ANY) {
        if (!okendpt(src_dst_e, &src_dst_slot)) {
            return 0; // Invalid endpoint, exit safely
        }
        
        xp = proc_addr(src_dst_slot);
        if (!proc_ptr_ok(xp) || RTS_ISSET(xp, RTS_SLOT_FREE)) {
            return 0; // Process pointer invalid or slot free, exit safely
        }
        
        group_size++;

        if ((src_dst_e = P_BLOCKEDON(xp)) == NONE) {
            return 0; // No deadlock found as chain breaks
        }

        if (src_dst_e == cp->p_endpoint) {
            return group_size; // Deadlock cycle found
        }
    }
    return 0; // No deadlock as we exit the loop
}

#include <stdio.h>
#include <stdbool.h>

#define DEBUG_ENABLE_IPC_WARNINGS 1
#define RTS_SENDING 0x04
#define ANY -1
#define NR_PROCS 256
#define NR_TASKS 64

struct proc {
	int p_rts_flags;
	char p_name[16];
	// Other fields...
};

typedef int endpoint_t;

int check_deadlock_cycle(struct proc *cp, endpoint_t src_dst_e);
int okendpt(endpoint_t e, int *proc_slot);
struct proc* proc_addr(int proc_slot);
endpoint_t P_BLOCKEDON(struct proc *p);
void print_proc(struct proc *p);
void proc_stacktrace(struct proc *p);

bool is_deadlock(struct proc *xp, int function) {
	return ((xp->p_rts_flags ^ (function << 2)) & RTS_SENDING) != 0;
}

void log_deadlock(struct proc *processes[], int group_size) {
	printf("deadlock between these processes:\n");
	for (int i = 0; i < group_size; i++) {
		printf(" %10s ", processes[i]->p_name);
	}
	printf("\n\n");
	for (int i = 0; i < group_size; i++) {
		print_proc(processes[i]);
		proc_stacktrace(processes[i]);
	}
}

int deadlock(int function, struct proc *cp, endpoint_t src_dst_e) {
	int group_size = check_deadlock_cycle(cp, src_dst_e);

	if (group_size == 2) {
		int src_dst_slot;
		if (okendpt(src_dst_e, &src_dst_slot) != 0) return group_size;

		struct proc *xp = proc_addr(src_dst_slot);
		if (is_deadlock(xp, function)) return 0;
	}

#if DEBUG_ENABLE_IPC_WARNINGS
	if (group_size > 0) {
		struct proc *processes[NR_PROCS + NR_TASKS];
		int src_dst_slot;
		int i = 0;

		processes[i++] = cp;
		while (src_dst_e != ANY && i < group_size) {
			if (okendpt(src_dst_e, &src_dst_slot) != 0) break;

			processes[i++] = proc_addr(src_dst_slot);
			src_dst_e = P_BLOCKEDON(processes[i - 1]);
		}

		log_deadlock(processes, group_size);
	}
#endif
	return group_size;
}

#include <stdbool.h>

#ifdef CONFIG_SMP
#include "proc.h" // Assuming proc_addr and RTS_ISSET macros and MF_SENDA_VM_MISS are defined here
#endif

#define NULL_PRIV_ID -1
#define ANY -1
#define NR_SYS_PROCS 64
#define BITCHUNK_BITS 32

static bool is_valid_src_id(int src_id);
static void handle_proc_flags_if_needed(int src_id, int asynm);

static int has_pending(sys_map_t *map, int src_p, int asynm) {
    int src_id = NULL_PRIV_ID;
    
    if (src_p != ANY) {
        src_id = nr_to_id(src_p);
        if (get_sys_bit(*map, src_id)) {
            handle_proc_flags_if_needed(src_id, asynm);
            return src_id;
        }
    } else {
        for (src_id = 0; src_id < NR_SYS_PROCS; src_id += BITCHUNK_BITS) {
            if (get_sys_bits(*map, src_id) != 0) {
                int inner_src_id;
                for (inner_src_id = src_id; inner_src_id < NR_SYS_PROCS && inner_src_id < src_id + BITCHUNK_BITS; ++inner_src_id) {
                    if (get_sys_bit(*map, inner_src_id)) {
                        if(is_valid_src_id(inner_src_id))
                            return inner_src_id;
                    }
                }
            }
        }
    }
    
    return NULL_PRIV_ID;
}

static void handle_proc_flags_if_needed(int src_id, int asynm) {
#ifdef CONFIG_SMP
    if (asynm) {
        struct proc *p = proc_addr(id_to_nr(src_id));
        if (RTS_ISSET(p, RTS_VMINHIBIT)) {
            p->p_misc_flags |= MF_SENDA_VM_MISS;
        }
    }
#endif
}

static bool is_valid_src_id(int src_id) {
#ifdef CONFIG_SMP
    struct proc *p = proc_addr(id_to_nr(src_id));
    return !RTS_ISSET(p, RTS_VMINHIBIT);
#else
    return true;
#endif
}

int has_pending_notify(struct proc *caller, int src_p) {
	if (caller == NULL) {
		return 0; // Proper error handling, null check
	}

	sys_map_t *map = &priv(caller)->s_notify_pending;
	return has_pending(map, src_p, 0);
}

int has_pending_asend(struct proc *caller, int src_p) {
	if (caller == NULL || priv(caller) == NULL) {
		return 0; // Error or no pending asynchronous send
	}
	sys_map_t *map = &priv(caller)->s_asyn_pending;
	if (map == NULL) {
		return 0; // Error or no pending asynchronous send
	}
	return has_pending(map, src_p, 1);
}

void unset_notify_pending(struct proc *caller, int src_p) {
	if (caller == NULL || src_p < 0) {
		return;
	}

	sys_map_t *map = &priv(caller)->s_notify_pending;
	if (map == NULL) {
		return;
	}

	unset_sys_bit(*map, src_p);
}

int mini_send(struct proc *caller_ptr, endpoint_t dst_e, message *m_ptr, int flags)
{
	struct proc *dst_ptr = proc_addr(_ENDPOINT_P(dst_e));
	struct proc **xpp;
	int call_result;

	if (RTS_ISSET(dst_ptr, RTS_NO_ENDPOINT)) return EDEADSRCDST;

	if (WILLRECEIVE(caller_ptr->p_endpoint, dst_ptr, (vir_bytes)m_ptr, NULL)) {
		if (dst_ptr->p_misc_flags & MF_DELIVERMSG) return EFAULT;
		
		if (!(flags & FROM_KERNEL)) {
			if (copy_msg_from_user(m_ptr, &dst_ptr->p_delivermsg)) return EFAULT;
		} else {
			dst_ptr->p_delivermsg = *m_ptr;
			IPC_STATUS_ADD_FLAGS(dst_ptr, IPC_FLG_MSG_FROM_KERNEL);
		}

		dst_ptr->p_delivermsg.m_source = caller_ptr->p_endpoint;
		dst_ptr->p_misc_flags |= MF_DELIVERMSG;

		call_result = (caller_ptr->p_misc_flags & MF_REPLY_PEND) ? SENDREC : 
					  (flags & NON_BLOCKING) ? SENDNB : SEND;
		IPC_STATUS_ADD_CALL(dst_ptr, call_result);

		if (caller_ptr->p_misc_flags & MF_REPLY_PEND) caller_ptr->p_misc_flags &= ~MF_REPLY_PEND;
		RTS_UNSET(dst_ptr, RTS_RECEIVING);

	} else {
		if (flags & NON_BLOCKING) return ENOTREADY;
		if (deadlock(SEND, caller_ptr, dst_e)) return ELOCKED;

		if (!(flags & FROM_KERNEL)) {
			if (copy_msg_from_user(m_ptr, &caller_ptr->p_sendmsg)) return EFAULT;
		} else {
			caller_ptr->p_sendmsg = *m_ptr;
			caller_ptr->p_misc_flags |= MF_SENDING_FROM_KERNEL;
		}

		RTS_SET(caller_ptr, RTS_SENDING);
		caller_ptr->p_sendto_e = dst_e;

		xpp = &dst_ptr->p_caller_q;
		while (*xpp) xpp = &(*xpp)->p_q_link;
		*xpp = caller_ptr;
	}

	return OK;
}

int check_pending_notifications(struct proc *caller_ptr, int src_p, endpoint_t src_e) {
    int src_id = has_pending_notify(caller_ptr, src_p);
    if (src_id == NULL_PRIV_ID) {
        return 0;
    }

    int src_proc_nr = id_to_nr(src_id);
    endpoint_t sender_e = proc_addr(src_proc_nr)->p_endpoint;

    if (!CANRECEIVE(src_e, sender_e, caller_ptr, 0, &m_notify_buff)) {
        return 0;
    }

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

static int check_async_messages(struct proc *caller_ptr, int src_p, endpoint_t src_e) {
    if (has_pending_asend(caller_ptr, src_p) == NULL_PRIV_ID) {
        return 0;
    }

    int r = (src_p != ANY) ? try_one(src_e, proc_addr(src_p), caller_ptr) 
                           : try_async(caller_ptr);

    if (r == OK) {
        IPC_STATUS_ADD_CALL(caller_ptr, SENDA);
        return 1;
    }

    return 0;
}

static int check_caller_queue(struct proc *caller_ptr, endpoint_t src_e) {
    struct proc **xpp = &caller_ptr->p_caller_q;
    
    while (*xpp) {
        struct proc *sender = *xpp;
        endpoint_t sender_e = sender->p_endpoint;

        if (!CANRECEIVE(src_e, sender_e, caller_ptr, 0, &sender->p_sendmsg)) {
            xpp = &sender->p_caller_q;
            continue;
        }

        assert(!RTS_ISSET(sender, RTS_SLOT_FREE));
        assert(!RTS_ISSET(sender, RTS_NO_ENDPOINT));

        assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));
        caller_ptr->p_delivermsg = sender->p_sendmsg;
        
        // Break loop once the proper sender is found
        return 1;
    }
    return 0;
}