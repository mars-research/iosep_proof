include "../x86/ins_eval_def.dfy"
include "../../mm/wk_mem.dfy"

/*********************** Predicates of external functions ********************/
// Predicate: SP and BP is unchanged
predicate {:opaque} ffi_preserve_sp_and_bp(old_wkm:WK_MState, new_regs:map<x86Reg, word>)
    requires Valid_WKMachineState_Arch(old_wkm)
{
    Valid_WKMState_RegsDecl(new_regs) &&
    x86_get_reg(old_wkm, ESP) == new_regs[ESP] &&
    x86_get_reg(old_wkm, EBP) == new_regs[EBP]
}

// Predicate: The external function only append values to the stack (stack for I/O separation part of WK Code) and write 
// return values on the stack
// <params_words_num> is the number of words should be modified by FFI
predicate {:opaque} ffi_preserve_old_stack(old_wkm:WK_MState, new_stack:wk_memmap, params_words_num:nat)
    requires Valid_WKMachineState_Arch(old_wkm)
    requires WK_ValidMemState(old_wkm)
{
    var esp := x86_get_reg(old_wkm, ESP); 
    var bottom_param_vaddr := esp + (params_words_num - 1) * ARCH_WORD_BYTES; 
        // input params and ret params use the same region of stack. The first param is at esp + 0

    x86wk_valid_memstate(new_stack) &&
    (forall vaddr:word :: IsAddrInStack(vaddr) && vaddr > bottom_param_vaddr   
            // For all stack below external functions stack and its return value. 
            // not >= w3_addr, because w3_addr also holds the return value
        ==> wkm_stack_get_val(old_wkm, vaddr) == stack_get_val(new_stack, vaddr))
            // old stack is unchanged
}