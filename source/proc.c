```c
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
static int mini_receive(struct proc *caller_ptr, endpoint_t src, message *m_buff_usr, int flags);
static int mini_senda(struct proc *caller_ptr, asynmsg_t *table, size_t size);
static int deadlock(struct proc *caller, endpoint_t src_dst_e, int is_send);
static int try_async(struct proc *caller_ptr);
static int try_one(endpoint_t receive_e, struct proc *src_ptr, struct proc *dst_ptr);
static struct proc * pick_proc(void);
static void enqueue_head(struct proc *rp);
static void delivermsg(struct proc *rp);
static int do_sync_ipc(struct proc *caller_ptr, int call_nr, endpoint_t src_dst_e, message *m_ptr);
static sys_id_t has_pending(sys_map_t *map, int src_p, int asynm);
static void notify_scheduler(struct proc *p);

static struct priv idle_priv;


static void set_idle_name(char *name, int n)
{
    int i = 4;
    n = (n > 999) ? 999 : n;
    memcpy(name, "idle", 4);
    for (; n > 0 || i == 4; n /= 10, i++) {
        name[i] = '0' + (n % 10);
    }
    name[i] = '\0';
}


void proc_init(void)
{
    int i;
    for (struct proc *rp = BEG_PROC_ADDR, *end = END_PROC_ADDR; rp < end; ++rp) {
        rp->p_rts_flags = RTS_SLOT_FREE;
        rp->p_magic = PMAGIC;
        rp->p_nr = BEG_PROC_ADDR - rp - NR_TASKS;
        rp->p_endpoint = _ENDPOINT(0, rp->p_nr);
        rp->p_scheduler = NULL;
        rp->p_priority = 0;
        rp->p_quantum_size_ms = 0;
        arch_proc_reset(rp);
    }

    for (struct priv *sp = BEG_PRIV_ADDR, *end = END_PRIV_ADDR; sp < end; ++sp) {
        sp->s_proc_nr = NONE;
        sp->s_id = sp - BEG_PRIV_ADDR;
        ppriv_addr[sp->s_id] = sp;
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
    if (priv(p)->s_flags & BILLABLE)
        get_cpulocal_var(bill_ptr) = p;

    switch_address_space_idle();

#ifdef CONFIG_SMP
    get_cpulocal_var(cpu_is_idle) = 1;
    if (cpuid != bsp_cpu_id)
        stop_local_timer();
    else
#endif
        restart_local_timer();

    context_stop(proc_addr(KERNEL));

#if !SPROFILE
    halt_cpu();
#else
    if (!sprofiling)
        halt_cpu();
    else {
        volatile int *idle_interrupted = get_cpulocal_var_ptr(idle_interrupted);
        interrupts_enable();
        while (!*idle_interrupted)
            arch_pause();
        interrupts_disable();
        *idle_interrupted = 0;
    }
#endif
}

void vm_suspend(struct proc *caller, const struct proc *target, const vir_bytes linaddr, const vir_bytes len, const int type, const int writeflag)
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
    vmrequest = caller;

    if(send_sig(VM_PROC_NR, SIGKMEM) != OK)
        panic("send_sig failed");
}

static void delivermsg(struct proc *rp)
{
    assert(!RTS_ISSET(rp, RTS_VMREQUEST));
    assert(rp->p_misc_flags & MF_DELIVERMSG);
    assert(rp->p_delivermsg.m_source != NONE);

    if (copy_msg_to_user(&rp->p_delivermsg, (message *) rp->p_delivermsg_vir) == OK) {
        rp->p_delivermsg.m_source = NONE;
        rp->p_misc_flags &= ~(MF_DELIVERMSG|MF_MSGFAILED);
        if(!(rp->p_misc_flags & MF_CONTEXT_SET)) {
            rp->p_reg.retreg = OK;
        }
    } else {
        if(rp->p_misc_flags & MF_MSGFAILED) {
            printf("WARNING wrong user pointer 0x%08lx from process %s / %d\n", rp->p_delivermsg_vir, rp->p_name, rp->p_endpoint);
            cause_sig(rp->p_nr, SIGSEGV);
        } else {
            vm_suspend(rp, rp, rp->p_delivermsg_vir, sizeof(message), VMSTYPE_DELIVERMSG, 1);
            rp->p_misc_flags |= MF_MSGFAILED;
        }
    }
}


void switch_to_user(void)
{
    struct proc *p = get_cpulocal_var(proc_ptr);
#ifdef CONFIG_SMP
    int tlb_must_refresh = 0;
#endif

pick_new_proc:

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
        if ((p->p_misc_flags & MF_FLUSH_TLB) && (get_cpulocal_var(ptproc) == p))
            tlb_must_refresh = 1;
#endif

        switch_address_space(p);
    }


    while (p->p_misc_flags & (MF_KCALL_RESUME | MF_DELIVERMSG | MF_SC_DEFER | MF_SC_TRACE | MF_SC_ACTIVE)) {
        assert(proc_is_runnable(p));

        if (p->p_misc_flags & MF_KCALL_RESUME) {
            kernel_call_resume(p);
        } else if (p->p_misc_flags & MF_DELIVERMSG) {
            TRACE(VF_SCHEDULING, printf("delivering to %s / %d\n", p->p_name, p->p_endpoint));
            delivermsg(p);
        } else if (p->p_misc_flags & MF_SC_DEFER) {
            assert (!(p->p_misc_flags & MF_SC_ACTIVE));
            arch_do_syscall(p);
            if ((p->p_misc_flags & MF_SIG_DELAY) && !RTS_ISSET(p, RTS_SENDING))
                sig_delay_done(p);
        } else if (p->p_misc_flags & MF_SC_TRACE) {
            if (p->p_misc_flags & MF_SC_ACTIVE) {
                p->p_misc_flags &= ~(MF_SC_TRACE | MF_SC_ACTIVE);
                cause_sig(proc_nr(p), SIGTRAP);
            } else break; 

        } else if (p->p_misc_flags & MF_SC_ACTIVE) {
            p->p_misc_flags &= ~MF_SC_ACTIVE;
            break;
        }


        if (!proc_is_runnable(p))
            goto pick_new_proc;
    }

    if (!p->p_cpu_time_left)
        proc_no_time(p);

    if (!proc_is_runnable(p))
        goto pick_new_proc;


    TRACE(VF_SCHEDULING, printf("cpu %d starting %s / %d pc 0x%08x\n", cpuid, p->p_name, p->p_endpoint, p->p_reg.pc));
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


static int do_sync_ipc(struct proc * caller_ptr, int call_nr, endpoint_t src_dst_e, message *m_ptr)
{
    int result, src_dst_p;
    char *callname = ipc_call_names[call_nr];


    if (call_nr < 0 || call_nr > IPCNO_HIGHEST || call_nr >= 32 || !callname) {
#if DEBUG_ENABLE_IPC_WARNINGS
        printf("sys_call: trap %d not allowed, caller %d, src_dst %d\n", call_nr, proc_nr(caller_ptr), src_dst_e);
#endif
        return ETRAPDENIED;
    }

    if (src_dst_e == ANY) {
        if (call_nr != RECEIVE) {
            return EINVAL;
        }
        src_dst_p = (int)src_dst_e;
    } else if(isokendpt(src_dst_e, &src_dst_p)) {
        if (call_nr != RECEIVE && !may_send_to(caller_ptr, src_dst_p)) {
#if DEBUG_ENABLE_IPC_WARNINGS
            printf("sys_call: ipc mask denied %s from %d to %d\n", callname, caller_ptr->p_endpoint, src_dst_e);
#endif
            return ECALLDENIED;
        }
    } else {
        return EDEADSRCDST;
    }



    if (!(priv(caller_ptr)->s_trap_mask & (1 << call_nr))) {
#if DEBUG_ENABLE_IPC_WARNINGS
        printf("sys_call: %s not allowed, caller %d, src_dst %d\n", callname, proc_nr(caller_ptr), src_dst_p);
#endif
        return ETRAPDENIED;
    }

    if (call_nr != SENDREC && call_nr != RECEIVE && iskerneln(src_dst_p)) {
#if DEBUG_ENABLE_IPC_WARNINGS
        printf("sys_call: trap %s not allowed, caller %d, src_dst %d\n", callname, proc_nr(caller_ptr), src_dst_e);
#endif
        return ETRAPDENIED;
    }

    switch(call_nr) {
    case SENDREC:
        caller_ptr->p_misc_flags |= MF_REPLY_PEND;
        /* fallthrough */
    case SEND:
        result = mini_send(caller_ptr, src_dst_e, m_ptr, 0);
        if (call_nr == SEND || result != OK)
            break;
        /* fallthrough for SENDREC */
    case RECEIVE:
        if (call_nr == RECEIVE) {
            caller_ptr->p_misc_flags &= ~MF_REPLY_PEND;
            IPC_STATUS_CLEAR(caller_ptr);
        }
        result = mini_receive(caller_ptr, src_dst_e, m_ptr, 0);
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
    struct proc *caller_ptr = get_cpulocal_var(proc_ptr);
    int call_nr = (int) r1;

    assert(!RTS_ISSET(caller_ptr, RTS_SLOT_FREE));

    kbill_ipc = caller_ptr;

    if (caller_ptr->p_misc_flags & MF_SC_TRACE) {
        if (!(caller_ptr->p_misc_flags & MF_SC_DEFER)) {
            caller_ptr->p_misc_flags |= MF_SC_DEFER;
            caller_ptr->p_defer.r1 = r1;
            caller_ptr->p_defer.r2 = r2;
            caller_ptr->p_defer.r3 = r3;
            cause_sig(proc_nr(caller_ptr), SIGTRAP);
            return caller_ptr->p_reg.retreg;
        }
        caller_ptr->p_misc_flags &= ~MF_SC_TRACE;

    }

    if (caller_ptr->p_misc_flags & MF_SC_DEFER) {
        caller_ptr->p_misc_flags &= ~MF_SC_DEFER;
        caller_ptr->p_misc_flags |= MF_SC_ACTIVE;
    }


    if(caller_ptr->p_misc_flags & MF_DELIVERMSG) {
        panic("sys_call: MF_DELIVERMSG on for %s / %d\n", caller_ptr->p_name, caller_ptr->p_endpoint);
    }

    switch(call_nr) {
    case SENDREC:
    case SEND:
    case RECEIVE:
    case NOTIFY:
    case SENDNB:
        caller_ptr->p_accounting.ipc_sync++;
        return do_sync_ipc(caller_ptr, call_nr, (endpoint_t) r2, (message *) r3);
    case SENDA: {
        size_t msg_size = (size_t) r2;
        caller_ptr->p_accounting.ipc_async++;
        if (msg_size > 16*(NR_TASKS + NR_PROCS))
            return EDOM;
        return mini_senda(caller_ptr, (asynmsg_t *) r3, msg_size);
    }
    case MINIX_KERNINFO:
        if(!minix_kerninfo_user)
            return EBADCALL;
        arch_set_secondary_ipc_return(caller_ptr, minix_kerninfo_user);
        return OK;

    default:
        return EBADCALL;
    }
}



static int deadlock(struct proc *cp, endpoint_t src_dst_e, int is_send)
{
    int group_size = 1;
    struct proc *xp;
#if DEBUG_ENABLE_IPC_WARNINGS
    struct proc *processes[NR_PROCS + NR_TASKS];
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
        group_size++;


        if((src_dst_e = P_BLOCKEDON(xp)) == NONE)
            return 0;


        if (src_dst_e == cp->p_endpoint) {
            if (group_size == 2 && ((xp->p_rts_flags >> 2) & RTS_SENDING) != is_send) {
                return 0;
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


static sys_id_t has_pending(sys_map_t *map, int src_p, int asynm)
{

    sys_id_t src_id = NULL_PRIV_ID;

    if (src_p != ANY) {
        if (get_sys_bit(*map, src_p)) {
#ifdef CONFIG_SMP
            struct proc *p = proc_addr(src_p);
            if (asynm && RTS_ISSET(p, RTS_VMINHIBIT))
                p->p_misc_flags |= MF_SENDA_VM_MISS;
            else
#endif
                src_id = src_p;
        }
    } else {
        for (int i = 0; i < NR_SYS_PROCS; i++) {
            if (get_sys_bit(*map, i)) {
#ifdef CONFIG_SMP
                struct proc *p = proc_addr(i);
                if (asynm && RTS_ISSET(p, RTS_VMINHIBIT)) {
                    p->p_misc_flags |= MF_SENDA_VM_MISS;
                } else
#endif
                {
                    src_id = i;
                    break;
                }
            }
        }
    }
    return src_id;
}


int has_pending_notify(struct proc * caller, int src_p)
{
    return has_pending(&priv(caller)->s_notify_pending, src_p, 0);
}


int has_pending_asend(struct proc * caller, int src_p)
{
    return has_pending(&priv(caller)->s_asyn_pending, src_p, 1);
}


void unset_notify_pending(struct proc * caller, int src_p)
{
    unset_sys_bit(priv(caller)->s_notify_pending, src_p);
}

int mini_send(struct proc *caller_ptr, endpoint_t dst_e, message *m_ptr, const int flags)
{
    struct proc *dst_ptr;
    int dst_p = _ENDPOINT_P(dst_e);

    dst_ptr = proc_addr(dst_p);

    if (RTS_ISSET(dst_ptr, RTS_NO_ENDPOINT)) {
        return EDEADSRCDST;
    }

    if (WILLRECEIVE(caller_ptr->p_endpoint, dst_ptr, (vir_bytes)m_ptr, NULL)) {
        int call;

        assert(!(dst_ptr->p_misc_flags & MF_DELIVERMSG));

        if (flags & FROM_KERNEL) {
            dst_ptr->p_delivermsg = *m_ptr;
            IPC_STATUS_ADD_FLAGS(dst_ptr, IPC_FLG_MSG_FROM_KERNEL);
        } else if(copy_msg_from_user(m_ptr, &dst_ptr->p_delivermsg)) {
            return EFAULT;
        }


        dst_ptr->p_delivermsg.m_source = caller_ptr->p_endpoint;
        dst_ptr->p_misc_flags |= MF_DELIVERMSG;

        call = (caller_ptr->p_misc_flags & MF_REPLY_PEND) ? SENDREC : ((flags & NON_BLOCKING) ? SENDNB : SEND);
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


        if (deadlock(caller_ptr, dst_e, 1)) {
            return ELOCKED;
        }


        if (flags & FROM_KERNEL) {
            caller_ptr->p_sendmsg = *m_ptr;
            caller_ptr->p_misc_flags |= MF_SENDING_FROM_KERNEL;
        } else if (copy_msg_from_user(m_ptr, &caller_ptr->p_sendmsg)) {
            return EFAULT;
        }

        RTS_SET(caller_ptr, RTS_SENDING);
        caller_ptr->p_sendto_e = dst_e;

        assert(caller_ptr->p_q_link == NULL);

        struct proc **xpp = &dst_ptr->p_caller_q;
        while (*xpp)
            xpp = &(*xpp)->p_q_link;

        *xpp = caller_ptr;

#if DEBUG_IPC_HOOK
        hook_ipc_msgsend(&caller_ptr->p_sendmsg, caller_ptr, dst_ptr);
#endif
    }

    return OK;
}


static int mini_receive(struct proc * caller_ptr, endpoint_t src_e, message * m_buff_usr, const int flags)
{
    struct proc **xpp;
    int r, src_proc_nr;
    endpoint_t sender_e;
    int src_p;
    sys_id_t src_id;

    assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));

    caller_ptr->p_delivermsg_vir = (vir_bytes) m_buff_usr;

    src_p = (src_e == ANY) ? ANY : _ENDPOINT_P(src_e);

    if (src_e != ANY && RTS_ISSET(proc_addr(src_p), RTS_NO_ENDPOINT)) {
        return EDEADSRCDST;
    }



    if (!RTS_ISSET(caller_ptr, RTS_SENDING)) {

        if (! (caller_ptr->p_misc_flags & MF_REPLY_PEND)) {

            src_id = has_pending_notify(caller_ptr, src_p);

            if (src_id != NULL_PRIV_ID) {
                src_proc_nr = src_id;
                sender_e = proc_addr(src_proc_nr)->p_endpoint;


                if (CANRECEIVE(src_e, sender_e, caller_ptr, 0, &m_notify_buff)) {
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

                    return OK;
                }
            }
        }


        if (has_pending_asend(caller_ptr, src_p) != NULL_PRIV_ID) {
            r = (src_p != ANY) ? try_one(src_e, proc_addr(src_p), caller_ptr) : try_async(caller_ptr);

            if (r == OK) {
                IPC_STATUS_ADD_CALL(caller_ptr, SENDA);
                return OK;
            }
        }


        xpp = &caller_ptr->p_caller_q;
        while (*xpp) {
            struct proc *sender = *xpp;
            sender_e = sender->p_endpoint;

            if (CANRECEIVE(src_e, sender_e, caller_ptr, 0, &sender->p_sendmsg)) {
                int call;
                assert(!RTS_ISSET(sender, RTS_SLOT_FREE));
                assert(!RTS_ISSET(sender, RTS_NO_ENDPOINT));

                assert(!(caller_ptr->p_misc_flags & MF_DELIVERMSG));
                caller_ptr->p_delivermsg = sender->p_sendmsg;
                caller_ptr->p_delivermsg.m_source = sender->p_endpoint;
                caller_ptr->p_misc_flags |= MF_DELIVERMSG;
                RTS_UNSET(sender, RTS_SENDING);

                call = (sender->p_misc_flags & MF_REPLY_PEND) ? SENDREC : SEND;
                IPC_STATUS_ADD_CALL(caller_ptr, call);


                if (sender->p_misc_flags & MF_SENDING_FROM_KERNEL) {
                    IPC_STATUS_ADD_FLAGS(caller_ptr, IPC_FLG_MSG_FROM_KERNEL);
                    sender->p_misc_flags &= ~MF_SENDING_FROM_KERNEL;
                }

                if (sender->p_misc_flags & MF_SIG_DELAY)
                    sig_delay_done(sender);

#if DEBUG_IPC_HOOK
                hook_ipc_msgrecv(&caller_ptr->p_delivermsg, sender, caller_ptr);
#endif

                *xpp = sender->p_q_link;
                sender->p_q_link = NULL;

                return OK;
            }

            xpp = &sender->p_q_link;
        }
    }


    if (!(flags & NON_BLOCKING)) {

        if (deadlock(caller_ptr, src_e, 0)) {
            return ELOCKED;
        }

        caller_ptr->p_getfrom_e = src_e;
        RTS_SET(caller_ptr, RTS_RECEIVING);
        return OK;
    }

    return ENOTREADY;
}


int mini_notify(const struct proc *caller_ptr, endpoint_t dst_e)
{
    struct proc *dst_ptr;
    sys_id_t src_id;
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

        BuildNotifyMessage(&dst_ptr->p_delivermsg, proc_nr(caller_ptr), dst_ptr);
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

#define ASCOMPLAIN(caller, entry, field)    \
    printf("kernel:%s:%d: asyn failed for %s in %s (%d/%zu, tab 0x%lx)\n", \
        __FILE__,__LINE__, field, caller->p_name, entry, priv(caller)->s_asynsize, priv(caller)->s_asyntab)

#define A_RETR(entry) do {    \
    if (data_copy(caller_ptr->p_endpoint, table_v + (entry)*sizeof(asynmsg_t), \
        KERNEL, (vir_bytes) &tabent, sizeof(tabent)) != OK) { \
        ASCOMPLAIN(caller_ptr, entry, "message entry"); \
        r = EFAULT;   \
        goto asyn_error; \
    } else if(tabent.dst == SELF) { \
        tabent.dst = caller_ptr->p_endpoint; \
    } \
} while(0)


#define A_INSRT(entry) do {   \
    if (data_copy(KERNEL, (vir_bytes) &tabent, \
        caller_ptr->p_endpoint, table_v + (entry)*sizeof(asynmsg_t), \
        sizeof(tabent)) != OK) { \
        ASCOMPLAIN(caller_ptr, entry, "message entry"); \
    }


