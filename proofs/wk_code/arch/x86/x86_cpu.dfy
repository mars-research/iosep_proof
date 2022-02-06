include "../../utils/common/headers.dfy"
include "x86_mstate.dfy"

/*********************** Interface Realization - Interrupt Flag Related ********************/
// Interface realization: <interrupts_enabled>
predicate interrupts_enabled(eflags:word)
    //requires is_valid_x86_sregs(wk_mstate.sregs)
{
    // reveal is_valid_x86_sregs();

    //var eflags := wk_mstate.sregs[EFLAGS];
    //BitwiseAnd(eflags, X86_EFLAGS_IF) != 0
    BitwiseAnd(eflags, X86_EFLAGS_IF) != 0
}

// Interface realization: <Valid_WKMState_RegsDecl>
predicate Valid_WKMState_RegsDecl(regs:map<x86Reg, word>)
{
    is_valid_x86_regs(regs)
}

predicate is_flags_unchanged(old_eflags:word, new_eflags:word)
{
    old_eflags == new_eflags
}




/*********************** Architecture Specific State Invariants and Related Predicates ********************/
predicate is_valid_x86_regs(regs:map<x86Reg, word>)
{   
    forall r:x86Reg :: r in regs
}   

predicate is_valid_x86_sregs(sregs:map<SReg, word>)
{
    (forall sr:SReg :: sr in sregs)
}

predicate is_exist_x86_reg(regs:map<x86Reg, word>, r:x86Reg)
{
    r in regs
}

predicate is_exist_x86_sreg(sregs:map<SReg, word>, r:SReg)
{
    r in sregs
}




/*********************** Other Definitions And Utility Functions ********************/
// See Intel® 64 and IA-32 Architectures Software Developer’s Manual, Section 3.4.3.1
const X86_EFLAGS_IF := 0x00000200; 

// Maximum shift bits 
const ARCH_Ins_SHIFT_MAX:int := 32;

function x86_get_reg(wkm:WK_MState, r:x86Reg) : word
    requires is_exist_x86_reg(wkm.regs, r)
{
    wkm.regs[r]
}

function x86_get_sreg(wkm:WK_MState, r:SReg) : word
    requires is_exist_x86_sreg(wkm.sregs, r)
{
    wkm.sregs[r]
}

function x86_get_eflags(wkm:WK_MState) : word
    requires is_valid_x86_sregs(wkm.sregs)
{
    x86_get_sreg(wkm, EFLAGS)
}