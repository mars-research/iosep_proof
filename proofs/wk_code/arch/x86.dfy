include "x86/x86_types.dfy"
include "x86/x86_mstate.dfy"
include "x86/x86_cpu.dfy"
include "x86/x86_mem.dfy"
include "x86/x86_globals.dfy"

/*********************** Interface Realization - Architecture Specific SIs and TCs ********************/

// Interface realization: <Valid_WKMachineState_Arch>
predicate Valid_WKMachineState_Arch(wkm:WK_MState)
{
    // WK's machine state must contain all CPU general registers and EFLAGS as special registers
    Valid_WKMState_RegsDecl(wkm.regs) &&
    is_valid_x86_sregs(wkm.sregs) &&

    // ESP stores a stack vaddr
    (
        var esp_value := x86_get_reg(wkm, ESP);
        is_valid_addr(esp_value) && is_valid_vaddr(esp_value) && is_vaddr_in_stack(esp_value)
    ) &&
    
    x86wk_valid_memstate(wkm.m) && 

    (true) // [TODO] Need rewritten
}









