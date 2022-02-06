include "drv.ffi.s.dfy"
include "../state_properties_validity.i.dfy"
include "../ins/util/ffi.i.dfy"

// Lemma: CALL_WimpDrv_DO_Clear ends up at a result state fulfilling ValidState_
lemma Lemma_ffi_wimpdrv_DO_clear_ResultStateIsValidState(s:state, r:state)
    requires ValidState(s)
    requires var s_wkm := s.wk_mstate; 
             var old_esp := x86_get_reg(s_wkm, ESP);
             IsAddrInStack(old_esp + FFI_WimpDrv_DO_Clear_StackParamsWords * ARCH_WORD_BYTES - ARCH_WORD_BYTES); 
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_wimpdrv_DO_clear(s, old_esp)

    requires var result := ffi_wimpdrv_DO_clear(s);
            var new_stack := result.0;
            var new_regs := result.1;
            var new_objs := result.2;
            r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack), objects := new_objs)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    // Prove validity of <wk_mstate>
    assert wkm_get_globals(s.wk_mstate) == wkm_get_globals(r.wk_mstate);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s.wk_mstate, r.wk_mstate);

    // Prove validity of other state variables
    reveal p_ffi_wimpdrv_DO_clear_retval();
    Lemma_WK_ValidSubjsObjs_HoldIfOnlyWimpDrvDOValsAreChangedInObjs(s, r);

    Lemma_ValidIDMappings_OnObjectModification_IfObjIDsAreUnchanged(s, r);

    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s,r);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
}

// Lemma: CALL_WimpDrv_CheckDOPAddrRange ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_wimpdrv_DO_check_paddr_range_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_WimpDrv_DO_CheckPAddrRange_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_WimpDrv_DO_CheckPAddrRange_ReturnWords)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    assert wkm_get_globals(s) == wkm_get_globals(r);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s,r);
}

// Lemma: CALL_WimpDrv_CheckDOPAddrRange ends up at a result state fulfilling ValidState
lemma Lemma_ffi_wimpdrv_DO_check_paddr_range_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_WimpDrv_DO_CheckPAddrRange_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_WimpDrv_DO_CheckPAddrRange_ReturnWords)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s,r);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
}