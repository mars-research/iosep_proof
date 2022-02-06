include "usb_tds.ffi.s.dfy"
include "../../../state_properties_validity.i.dfy"
include "../usb_pdev.i.dfy"
include "../eehci_mem.i.dfy"
include "../usb_tds.i.dfy"
include "../../../ins/util/ffi.i.dfy"
include "../../../drv/public/wimpdrv_lemmas.i.dfy"

// Lemma: CALL_USBTD_QTD32_ParseTDPointers ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_usbtd_qtd32_parseQTDpointer_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_Qtd32_ParseQTDPointers_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    assert wkm_get_globals(s) == wkm_get_globals(r);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s,r);
}

// Lemma: CALL_USBTD_QTD32_ParseTDPointers ends up at a result state fulfilling ValidState
lemma Lemma_ffi_usbtd_qtd32_parseQTDpointer_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_Qtd32_ParseQTDPointers_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords)

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

// Lemma: CALL_USBTD_QTD32_ParseBufPointers ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_usbtd_qtd32_parseBufpointer_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_Qtd32_ParseBufPointers_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    assert wkm_get_globals(s) == wkm_get_globals(r);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s,r);
}

// Lemma: CALL_USBTD_QTD32_ParseBufPointers ends up at a result state fulfilling ValidState
lemma Lemma_ffi_usbtd_qtd32_parseBufpointer_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_Qtd32_ParseBufPointers_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords)

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

lemma Lemma_p_ffi_usbtd_qtd32_parseQTDpointers_retval_ImpliesDefinedProperties(
    old_wkm:WK_MState, new_stack:wk_memmap, old_esp:vaddr, old_stack:wk_memmap, old_globals:globalsmap
)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Qtd32_ParseQTDPointers_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords) // Words for return parameters
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm); 
            var td_slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(td_slot)
        // Requirement: The USB qTD referred by <td_slot> must be stored in <g_usbtd_map_mem>

    requires old_esp == x86_get_reg(old_wkm, ESP)
    requires old_stack == wkm_stack_get_all(old_wkm)
    requires old_globals == wkm_get_globals(old_wkm)

    requires p_ffi_usbtd_qtd32_parseTDPtrs_retval(old_wkm, new_stack)

    ensures x86wk_valid_memstate(new_stack)
    ensures var td_slot := stack_get_val(old_stack, old_esp);
            var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
            var out_next_qtd_slot:word := stack_get_val(new_stack, old_esp + 1 * ARCH_WORD_BYTES);
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), td_vaddr) &&
            out_next_qtd_slot == RightShift(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS);
    ensures var td_slot := stack_get_val(old_stack, old_esp);
            var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
            var out_alt_next_qtd_p:word := stack_get_val(new_stack, old_esp);
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES) &&
            out_alt_next_qtd_p == RightShift(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
{
    reveal p_ffi_usbtd_qtd32_parseTDPtrs_retval();

    var td_slot := stack_get_val(old_stack, old_esp);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + UINT32_BYTES);
}

// Lemma: CALL_USBTD_QH32_ParseTDPointers ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_usbtd_qh32_parseQTDpointer_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_Qh32_ParseTDPtrs_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_USBTD_Qh32_ParseTDPtrs_ReturnWords)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    assert wkm_get_globals(s) == wkm_get_globals(r);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s,r);
}

// Lemma: CALL_USBTD_QH32_ParseTDPointers ends up at a result state fulfilling ValidState
lemma Lemma_ffi_usbtd_qh32_parseQTDpointer_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_Qh32_ParseTDPtrs_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_USBTD_Qh32_ParseTDPtrs_ReturnWords)

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

// Lemma: CALL_USBTD_QH32_ParseBufPointers ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_usbtd_qh32_parseBufpointer_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_Qh32_ParseDataBufPtrs_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_USBTD_Qh32_ParseDataBufPtrs_ReturnWords)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    assert wkm_get_globals(s) == wkm_get_globals(r);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s,r);
}

// Lemma: CALL_USBTD_QH32_ParseBufPointers ends up at a result state fulfilling ValidState
lemma Lemma_ffi_usbtd_qh32_parseBufpointer_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_Qh32_ParseDataBufPtrs_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_USBTD_Qh32_ParseDataBufPtrs_ReturnWords)

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

// Lemma: CALL_USBTD_QH32_ParseTargetUSBDevID ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_usbtd_qh32_parseTargetUSBDevID_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_Qh32_ParseTargetUSBDevID_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_USBTD_Qh32_ParseTargetUSBDevID_ReturnWords)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    assert wkm_get_globals(s) == wkm_get_globals(r);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s,r);
}

// Lemma: CALL_USBTD_QH32_ParseTargetUSBDevID ends up at a result state fulfilling ValidState
lemma Lemma_ffi_usbtd_qh32_parseTargetUSBDevID_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_Qh32_ParseTargetUSBDevID_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_USBTD_Qh32_ParseTargetUSBDevID_ReturnWords)

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

// Lemma: if <ffi_usbtd_copy_from_user_copied_some_new_usbtd> is true, then other fields in <g_usbtd_mem_map> is unmodified
// [NOTE] Needs 40s to verify
lemma Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem(old_globals:globalsmap, new_globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbtd_map_valid_slot_id(slot)

    requires ffi_usbtd_copy_from_user_copied_some_new_usbtd(old_globals, new_globals, slot)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM && i != slot ==> p_usbtd_equal(old_globals, new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM && i != slot ==> p_usbtd_content_equal(old_globals, new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_idword(old_globals, i) == usbtd_map_get_idword(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_pid(old_globals, i) == usbtd_map_get_pid(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_type(old_globals, i) == usbtd_map_get_type(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_busid_word(old_globals, i) == usbtd_map_get_busid_word(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_flags(old_globals, i) == usbtd_map_get_flags(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_wimpdrv_slotid(old_globals, i) == usbtd_map_get_wimpdrv_slotid(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_usbpdev_slotid(old_globals, i) == usbtd_map_get_usbpdev_slotid(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_handle(old_globals, i) == usbtd_map_get_handle(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_inputparam(old_globals, i, G_USBTDs_MAP_ENTRY_InputParam1) == usbtd_map_get_inputparam(new_globals, i, G_USBTDs_MAP_ENTRY_InputParam1)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_inputparam(old_globals, i, G_USBTDs_MAP_ENTRY_InputParam2) == usbtd_map_get_inputparam(new_globals, i, G_USBTDs_MAP_ENTRY_InputParam2)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_inputparam(old_globals, i, G_USBTDs_MAP_ENTRY_InputParam3) == usbtd_map_get_inputparam(new_globals, i, G_USBTDs_MAP_ENTRY_InputParam3)
{
    reveal ffi_usbtd_copy_from_user_copied_some_new_usbtd();
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_WK_USB_TD_Map_PropertiesOfTDAddrs(slot);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 22 * UINT32_BYTES);

    var new_vals:seq<uint32> :| |new_vals| == MAX_USB_TD_BYTES/UINT32_BYTES &&
        (
            var new_globals1 := global_write_at_vaddr32(old_globals, G_USBTD_MAP_MEM(), td_addr, new_vals[0]);
            var new_globals2 := global_write_at_vaddr32(new_globals1, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES, new_vals[1]);
            var new_globals3 := global_write_at_vaddr32(new_globals2, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES, new_vals[2]);
            var new_globals4 := global_write_at_vaddr32(new_globals3, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES, new_vals[3]);
            var new_globals5 := global_write_at_vaddr32(new_globals4, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES, new_vals[4]);

            var new_globals6 := global_write_at_vaddr32(new_globals5, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES, new_vals[5]);
            var new_globals7 := global_write_at_vaddr32(new_globals6, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES, new_vals[6]);
            var new_globals8 := global_write_at_vaddr32(new_globals7, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES, new_vals[7]);
            var new_globals9 := global_write_at_vaddr32(new_globals8, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES, new_vals[8]);
            var new_globals10 := global_write_at_vaddr32(new_globals9, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES, new_vals[9]);

            var new_globals11 := global_write_at_vaddr32(new_globals10, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES, new_vals[10]);
            var new_globals12 := global_write_at_vaddr32(new_globals11, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES, new_vals[11]);
            var new_globals13 := global_write_at_vaddr32(new_globals12, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES, new_vals[12]);
            var new_globals14 := global_write_at_vaddr32(new_globals13, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES, new_vals[13]);
            var new_globals15 := global_write_at_vaddr32(new_globals14, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES, new_vals[14]);

            var new_globals16 := global_write_at_vaddr32(new_globals15, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES, new_vals[15]);
            var new_globals17 := global_write_at_vaddr32(new_globals16, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES, new_vals[16]);
            var new_globals18 := global_write_at_vaddr32(new_globals17, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES, new_vals[17]);
            var new_globals19 := global_write_at_vaddr32(new_globals18, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES, new_vals[18]);
            var new_globals20 := global_write_at_vaddr32(new_globals19, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES, new_vals[19]);

            var new_globals21 := global_write_at_vaddr32(new_globals20, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES, new_vals[20]);
            var new_globals22 := global_write_at_vaddr32(new_globals21, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES, new_vals[21]);
            var new_globals23 := global_write_at_vaddr32(new_globals22, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES, new_vals[22]);

            new_globals == new_globals23
        );

    var new_globals1 := global_write_at_vaddr32(old_globals, G_USBTD_MAP_MEM(), td_addr, new_vals[0]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(old_globals, new_globals1, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset, new_vals[0]);
    var new_globals2 := global_write_at_vaddr32(new_globals1, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES, new_vals[1]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals1, new_globals2, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 1 * UINT32_BYTES, new_vals[1]);
    var new_globals3 := global_write_at_vaddr32(new_globals2, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES, new_vals[2]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals2, new_globals3, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 2 * UINT32_BYTES, new_vals[2]);
    var new_globals4 := global_write_at_vaddr32(new_globals3, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES, new_vals[3]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals3, new_globals4, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 3 * UINT32_BYTES, new_vals[3]);
    var new_globals5 := global_write_at_vaddr32(new_globals4, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES, new_vals[4]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals4, new_globals5, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 4 * UINT32_BYTES, new_vals[4]);

    var new_globals6 := global_write_at_vaddr32(new_globals5, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES, new_vals[5]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals5, new_globals6, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 5 * UINT32_BYTES, new_vals[5]);
    var new_globals7 := global_write_at_vaddr32(new_globals6, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES, new_vals[6]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals6, new_globals7, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 6 * UINT32_BYTES, new_vals[6]);
    var new_globals8 := global_write_at_vaddr32(new_globals7, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES, new_vals[7]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals7, new_globals8, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 7 * UINT32_BYTES, new_vals[7]);
    var new_globals9 := global_write_at_vaddr32(new_globals8, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES, new_vals[8]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals8, new_globals9, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 8 * UINT32_BYTES, new_vals[8]);
    var new_globals10 := global_write_at_vaddr32(new_globals9, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES, new_vals[9]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals9, new_globals10, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 9 * UINT32_BYTES, new_vals[9]);

    var new_globals11 := global_write_at_vaddr32(new_globals10, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES, new_vals[10]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals10, new_globals11, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 10 * UINT32_BYTES, new_vals[10]);
    var new_globals12 := global_write_at_vaddr32(new_globals11, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES, new_vals[11]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals11, new_globals12, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 11 * UINT32_BYTES, new_vals[11]);
    var new_globals13 := global_write_at_vaddr32(new_globals12, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES, new_vals[12]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals12, new_globals13, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 12 * UINT32_BYTES, new_vals[12]);
    var new_globals14 := global_write_at_vaddr32(new_globals13, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES, new_vals[13]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals13, new_globals14, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 13 * UINT32_BYTES, new_vals[13]);
    var new_globals15 := global_write_at_vaddr32(new_globals14, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES, new_vals[14]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals14, new_globals15, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 14 * UINT32_BYTES, new_vals[14]);

    var new_globals16 := global_write_at_vaddr32(new_globals15, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES, new_vals[15]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals15, new_globals16, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 15 * UINT32_BYTES, new_vals[15]);
    var new_globals17 := global_write_at_vaddr32(new_globals16, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES, new_vals[16]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals16, new_globals17, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 16 * UINT32_BYTES, new_vals[16]);
    var new_globals18 := global_write_at_vaddr32(new_globals17, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES, new_vals[17]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals17, new_globals18, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 17 * UINT32_BYTES, new_vals[17]);
    var new_globals19 := global_write_at_vaddr32(new_globals18, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES, new_vals[18]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals18, new_globals19, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 18 * UINT32_BYTES, new_vals[18]);
    var new_globals20 := global_write_at_vaddr32(new_globals19, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES, new_vals[19]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals19, new_globals20, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 19 * UINT32_BYTES, new_vals[19]);

    var new_globals21 := global_write_at_vaddr32(new_globals20, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES, new_vals[20]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals20, new_globals21, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 20 * UINT32_BYTES, new_vals[20]);
    var new_globals22 := global_write_at_vaddr32(new_globals21, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES, new_vals[21]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals21, new_globals22, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 21 * UINT32_BYTES, new_vals[21]);
    var new_globals23 := global_write_at_vaddr32(new_globals22, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES, new_vals[22]);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(new_globals22, new_globals23, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 22 * UINT32_BYTES, new_vals[22]);

    assert new_globals == new_globals23;

    forall i:uint32 | usbtd_map_valid_slot_id(i) && i != slot
        ensures p_usbtd_content_equal(old_globals, new_globals, i)
    {
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals1, new_globals2, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals2, new_globals3, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals3, new_globals4, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals4, new_globals5, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals5, new_globals6, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals6, new_globals7, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals7, new_globals8, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals8, new_globals9, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals9, new_globals10, i);

        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals10, new_globals11, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals11, new_globals12, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals12, new_globals13, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals13, new_globals14, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals14, new_globals15, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals15, new_globals16, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals16, new_globals17, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals17, new_globals18, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals18, new_globals19, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals19, new_globals20, i);

        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals20, new_globals21, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals21, new_globals22, i);
        Lemma_p_usbtd_content_equal_transitive(old_globals, new_globals22, new_globals, i);
    }
}

// Lemma: if <ffi_usbtd_copy_from_user_copied_some_new_usbtd> is true, then other fields in <g_usbtd_mem_map> is unmodified
lemma Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherUSBTDs(old_globals:globalsmap, new_globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbtd_map_valid_slot_id(slot)

    requires ffi_usbtd_copy_from_user_copied_some_new_usbtd(old_globals, new_globals, slot)

    ensures forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != slot
        ==> p_usbtd_equal(old_globals, new_globals, i)
{
    reveal ffi_usbtd_copy_from_user_copied_some_new_usbtd();
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_WK_USB_TD_Map_PropertiesOfTDAddrs(slot);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 22 * UINT32_BYTES);

    var new_vals:seq<uint32> :| |new_vals| == MAX_USB_TD_BYTES/UINT32_BYTES &&
        (
            var new_globals1 := global_write_at_vaddr32(old_globals, G_USBTD_MAP_MEM(), td_addr, new_vals[0]);
            var new_globals2 := global_write_at_vaddr32(new_globals1, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES, new_vals[1]);
            var new_globals3 := global_write_at_vaddr32(new_globals2, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES, new_vals[2]);
            var new_globals4 := global_write_at_vaddr32(new_globals3, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES, new_vals[3]);
            var new_globals5 := global_write_at_vaddr32(new_globals4, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES, new_vals[4]);

            var new_globals6 := global_write_at_vaddr32(new_globals5, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES, new_vals[5]);
            var new_globals7 := global_write_at_vaddr32(new_globals6, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES, new_vals[6]);
            var new_globals8 := global_write_at_vaddr32(new_globals7, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES, new_vals[7]);
            var new_globals9 := global_write_at_vaddr32(new_globals8, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES, new_vals[8]);
            var new_globals10 := global_write_at_vaddr32(new_globals9, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES, new_vals[9]);

            var new_globals11 := global_write_at_vaddr32(new_globals10, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES, new_vals[10]);
            var new_globals12 := global_write_at_vaddr32(new_globals11, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES, new_vals[11]);
            var new_globals13 := global_write_at_vaddr32(new_globals12, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES, new_vals[12]);
            var new_globals14 := global_write_at_vaddr32(new_globals13, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES, new_vals[13]);
            var new_globals15 := global_write_at_vaddr32(new_globals14, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES, new_vals[14]);

            var new_globals16 := global_write_at_vaddr32(new_globals15, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES, new_vals[15]);
            var new_globals17 := global_write_at_vaddr32(new_globals16, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES, new_vals[16]);
            var new_globals18 := global_write_at_vaddr32(new_globals17, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES, new_vals[17]);
            var new_globals19 := global_write_at_vaddr32(new_globals18, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES, new_vals[18]);
            var new_globals20 := global_write_at_vaddr32(new_globals19, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES, new_vals[19]);

            var new_globals21 := global_write_at_vaddr32(new_globals20, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES, new_vals[20]);
            var new_globals22 := global_write_at_vaddr32(new_globals21, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES, new_vals[21]);
            var new_globals23 := global_write_at_vaddr32(new_globals22, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES, new_vals[22]);

            new_globals == new_globals23
        );

    assert isUInt32(G_USBTDs_MAP_ENTRY_TD_BytesOffset + 22 * UINT32_BYTES);

    var new_globals1 := global_write_at_vaddr32(old_globals, G_USBTD_MAP_MEM(), td_addr, new_vals[0]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(old_globals, new_globals1, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset, new_vals[0]);
    var new_globals2 := global_write_at_vaddr32(new_globals1, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES, new_vals[1]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals1, new_globals2, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 1 * UINT32_BYTES, new_vals[1]);
    var new_globals3 := global_write_at_vaddr32(new_globals2, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES, new_vals[2]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals2, new_globals3, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 2 * UINT32_BYTES, new_vals[2]);
    var new_globals4 := global_write_at_vaddr32(new_globals3, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES, new_vals[3]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals3, new_globals4, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 3 * UINT32_BYTES, new_vals[3]);
    var new_globals5 := global_write_at_vaddr32(new_globals4, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES, new_vals[4]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals4, new_globals5, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 4 * UINT32_BYTES, new_vals[4]);

    var new_globals6 := global_write_at_vaddr32(new_globals5, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES, new_vals[5]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals5, new_globals6, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 5 * UINT32_BYTES, new_vals[5]);
    var new_globals7 := global_write_at_vaddr32(new_globals6, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES, new_vals[6]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals6, new_globals7, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 6 * UINT32_BYTES, new_vals[6]);
    var new_globals8 := global_write_at_vaddr32(new_globals7, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES, new_vals[7]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals7, new_globals8, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 7 * UINT32_BYTES, new_vals[7]);
    var new_globals9 := global_write_at_vaddr32(new_globals8, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES, new_vals[8]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals8, new_globals9, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 8 * UINT32_BYTES, new_vals[8]);
    var new_globals10 := global_write_at_vaddr32(new_globals9, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES, new_vals[9]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals9, new_globals10, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 9 * UINT32_BYTES, new_vals[9]);

    var new_globals11 := global_write_at_vaddr32(new_globals10, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES, new_vals[10]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals10, new_globals11, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 10 * UINT32_BYTES, new_vals[10]);
    var new_globals12 := global_write_at_vaddr32(new_globals11, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES, new_vals[11]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals11, new_globals12, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 11 * UINT32_BYTES, new_vals[11]);
    var new_globals13 := global_write_at_vaddr32(new_globals12, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES, new_vals[12]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals12, new_globals13, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 12 * UINT32_BYTES, new_vals[12]);
    var new_globals14 := global_write_at_vaddr32(new_globals13, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES, new_vals[13]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals13, new_globals14, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 13 * UINT32_BYTES, new_vals[13]);
    var new_globals15 := global_write_at_vaddr32(new_globals14, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES, new_vals[14]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals14, new_globals15, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 14 * UINT32_BYTES, new_vals[14]);

    var new_globals16 := global_write_at_vaddr32(new_globals15, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES, new_vals[15]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals15, new_globals16, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 15 * UINT32_BYTES, new_vals[15]);
    var new_globals17 := global_write_at_vaddr32(new_globals16, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES, new_vals[16]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals16, new_globals17, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 16 * UINT32_BYTES, new_vals[16]);
    var new_globals18 := global_write_at_vaddr32(new_globals17, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES, new_vals[17]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals17, new_globals18, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 17 * UINT32_BYTES, new_vals[17]);
    var new_globals19 := global_write_at_vaddr32(new_globals18, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES, new_vals[18]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals18, new_globals19, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 18 * UINT32_BYTES, new_vals[18]);
    var new_globals20 := global_write_at_vaddr32(new_globals19, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES, new_vals[19]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals19, new_globals20, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 19 * UINT32_BYTES, new_vals[19]);

    var new_globals21 := global_write_at_vaddr32(new_globals20, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES, new_vals[20]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals20, new_globals21, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 20 * UINT32_BYTES, new_vals[20]);
    var new_globals22 := global_write_at_vaddr32(new_globals21, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES, new_vals[21]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals21, new_globals22, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 21 * UINT32_BYTES, new_vals[21]);
    var new_globals23 := global_write_at_vaddr32(new_globals22, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES, new_vals[22]);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(new_globals22, new_globals23, slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 22 * UINT32_BYTES, new_vals[22]);

    assert new_globals == new_globals23;

    forall i:uint32 | usbtd_map_valid_slot_id(i) && i != slot
        ensures p_usbtd_equal(old_globals, new_globals, i)
    {
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals1, new_globals2, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals2, new_globals3, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals3, new_globals4, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals4, new_globals5, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals5, new_globals6, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals6, new_globals7, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals7, new_globals8, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals8, new_globals9, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals9, new_globals10, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals10, new_globals11, i);

        Lemma_p_usbtd_equal_transitive(old_globals, new_globals11, new_globals12, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals12, new_globals13, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals13, new_globals14, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals14, new_globals15, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals15, new_globals16, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals16, new_globals17, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals17, new_globals18, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals18, new_globals19, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals19, new_globals20, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals20, new_globals21, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals21, new_globals22, i);
        Lemma_p_usbtd_equal_transitive(old_globals, new_globals22, new_globals23, i);
    }
}

// Lemma: CALL_USBTD_Copy_From_User ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_usbtd_copy_from_user_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, 1)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_usbtd_copy_from_user_stack_and_globals(s, new_stack, new_globals)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_copy_from_user_stack_and_globals();
    reveal ffi_usbtd_copy_from_user_copied_some_new_usbtd();

    var old_esp := x86_get_reg(s, ESP);
    var old_stack := wkm_stack_get_all(s);
    var old_globals := wkm_get_globals(s);

    var slot:word := stack_get_val(old_stack, old_esp);
    var ret:word := stack_get_val(new_stack, old_esp);


    if(ret == TRUE)
    {
        assert ffi_usbtd_copy_from_user_copied_some_new_usbtd(old_globals, new_globals, slot);
        Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem(old_globals, new_globals, slot);
        assert global_read_fullval(old_globals, G_Existing_PIDs()) == global_read_fullval(new_globals, G_Existing_PIDs());

        Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGExistingPIDsAndPIDCounterUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

        Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

        Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));

        Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(wkm_get_globals(s), wkm_get_globals(r));
        assert WK_ValidMState(r);
    }
    else
    {
        assert WK_ValidMState(r);
    }
}

// Lemma: CALL_USBTD_Copy_From_User ends up at a result state fulfilling ValidState
lemma Lemma_ffi_usbtd_copy_from_user_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap)
   requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, 1)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_usbtd_copy_from_user_stack_and_globals(s.wk_mstate, new_stack, new_globals)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_copy_from_user_stack_and_globals();
    reveal ffi_usbtd_copy_from_user_copied_some_new_usbtd();

    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s,r);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    
    Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(s,r);
    Lemma_WK_ValidGlobalVarValues_USBPDevList_OnWKMStateSubjectsModification_IfUSBPDevListIsUnchanged(s,r);

    Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_PEHCIs_OnSubjsExceptOSDevsModification(s, r);
}

// Lemma: CALL_USBTD_Copy_From_User ends up at a result state fulfilling WK_ValidMState and WK_EEHCI_Mem_SecureGlobalVarValues
lemma Lemma_ffi_usbtd_copy_from_user_ResultStateIsValidMState_AndEEHCIMemSecureState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(s)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(wkm_get_globals(s))
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, 1)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_usbtd_copy_from_user_stack_and_globals(s, new_stack, new_globals)

    ensures WK_ValidMState(r)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(wkm_get_globals(r))
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_copy_from_user_stack_and_globals();
    reveal ffi_usbtd_copy_from_user_copied_some_new_usbtd();

    var old_esp := x86_get_reg(s, ESP);
    var old_stack := wkm_stack_get_all(s);
    var old_globals := wkm_get_globals(s);

    var slot:word := stack_get_val(old_stack, old_esp);
    var ret:word := stack_get_val(new_stack, old_esp);


    if(ret == TRUE)
    {
        assert ffi_usbtd_copy_from_user_copied_some_new_usbtd(old_globals, new_globals, slot);
        Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem(old_globals, new_globals, slot);
        assert global_read_fullval(old_globals, G_Existing_PIDs()) == global_read_fullval(new_globals, G_Existing_PIDs());

        Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGExistingPIDsAndPIDCounterUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

        Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

        Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));

        Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));
        Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(wkm_get_globals(s), wkm_get_globals(r));
        assert WK_ValidMState(r);
    }
    else
    {
        assert WK_ValidMState(r);
    }
}

// Lemma: CALL_USBTD_Copy_From_User ends up at a result state fulfilling WK_SecureObjsAddrs_MemSeparation
lemma Lemma_ffi_usbtd_copy_from_user_ResultState_Prove_WK_SecureObjsAddrs_MemSeparation(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(s.wk_mstate)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate))

    requires WK_ValidGlobalState(wkm_get_globals(r.wk_mstate))
    requires WK_ValidSubjs(r.subjects, r.id_mappings)
    requires WK_ValidIDMappings(r.subjects, r.objects, r.id_mappings)
    requires WK_ValidObjs(r.subjects, r.objects)
    requires WK_ValidObjsAddrs(r.objects, r.objs_addrs, wkm_get_globals(r.wk_mstate))
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(r.subjects, r.objects, r.id_mappings, wkm_get_globals(r.wk_mstate))

    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, 1)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_usbtd_copy_from_user_stack_and_globals(s.wk_mstate, new_stack, new_globals)

    ensures WK_SecureObjsAddrs_MemSeparation(r.subjects, r.objects, r.id_mappings, r.objs_addrs, new_globals)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_copy_from_user_stack_and_globals();
    reveal ffi_usbtd_copy_from_user_copied_some_new_usbtd();

    Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s, r);
}

// Lemma: CALL_USBTD_Copy_From_User does not modify other global variables
lemma Lemma_ffi_usbtd_copy_from_user_DoNotModifyOtherGlobalVariables(
    s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, 1)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires ffi_usbtd_copy_from_user_stack_and_globals(s, new_stack, new_globals)

    ensures globals_other_gvar_unchanged(wkm_get_globals(s), wkm_get_globals(r), G_USBTD_MAP_MEM())
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_copy_from_user_stack_and_globals();
    reveal ffi_usbtd_copy_from_user_copied_some_new_usbtd();
}

// Lemma: CALL_USBTD_Copy_From_User does not modify flags, and modify one USB TD only
lemma Lemma_ffi_usbtd_copy_from_user_DoNotModifyFlagsAndOtherUSBTDs(
    s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, 1)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires x86wk_valid_memstate(new_stack)

    requires var old_esp := x86_get_reg(s, ESP);
            var old_stack := wkm_stack_get_all(s); 
            var slot := stack_get_val(old_stack, old_esp);
            usbtd_map_valid_slot_id(slot)

    requires ffi_usbtd_copy_from_user_stack_and_globals(s, new_stack, new_globals)

    ensures var old_esp := x86_get_reg(s, ESP);
            var old_stack := wkm_stack_get_all(s); 
            var slot := stack_get_val(old_stack, old_esp);
            var ret:word := stack_get_val(new_stack, old_esp);
            (ret == TRUE) ==> usbtd_map_get_flags(wkm_get_globals(s), slot) == usbtd_map_get_flags(new_globals, slot)

    ensures var old_esp := x86_get_reg(s, ESP);
            var old_stack := wkm_stack_get_all(s); 
            var slot := stack_get_val(old_stack, old_esp);
            var ret:word := stack_get_val(new_stack, old_esp);
            (ret == TRUE) ==> usbtd_map_modify_one_usbtd_only(wkm_get_globals(s), new_globals, slot)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_copy_from_user_stack_and_globals();
    reveal ffi_usbtd_copy_from_user_copied_some_new_usbtd();

    var old_globals := wkm_get_globals(s);
    var old_esp := x86_get_reg(s, ESP);
    var old_stack := wkm_stack_get_all(s); 
    var slot := stack_get_val(old_stack, old_esp);
    var ret:word := stack_get_val(new_stack, old_esp);

    if(ret == TRUE)
    {
        Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem(old_globals, new_globals, slot);
        Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherUSBTDs(old_globals, new_globals, slot);
    }
}

lemma Lemma_ffi_usbtd_copy_from_user_stack_and_globals_Properties(old_wkm:WK_MState, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_old_stack(old_wkm, new_stack, FFI_USBTD_CopyFromUser_ReturnWords) // Return parameters take 1 word 
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires x86wk_valid_memstate(new_stack)

    requires ffi_usbtd_copy_from_user_stack_and_globals(old_wkm, new_stack, new_globals)

    ensures var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm);
            var wimpdrv_slot_id:word := stack_get_val(old_stack, old_esp + 1 * ARCH_WORD_BYTES);
            var ret:word := stack_get_val(new_stack, old_esp);
            (ret == TRUE) ==> wimpdrv_valid_slot_id(wimpdrv_slot_id)
{
    reveal ffi_usbtd_copy_from_user_stack_and_globals();
}

// Lemma: <ffi_usbtd_copy_from_user> satisfies the security property <WK_USBTD_Map_SecureGlobalVarValues>
lemma Lemma_ffi_usbtd_copy_from_user_ProveSecurityProperty_WK_USBTD_Map_SecureGlobalVarValues(
    s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, 1)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires ffi_usbtd_copy_from_user_stack_and_globals(s, new_stack, new_globals)
        // Requirement: <ffi_usbtd_copy_from_user> transits states correctly

    requires WK_USBTD_Map_ValidGlobalVarValues(new_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(new_globals)
    requires WK_USBTD_Map_SecureGlobalVarValues(wkm_get_globals(s))

    ensures WK_USBTD_Map_SecureGlobalVarValues(new_globals) 
{
    reveal ffi_usbtd_copy_from_user_stack_and_globals();
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    var old_esp := x86_get_reg(s, ESP);
    var old_stack := wkm_stack_get_all(s);
    var old_globals := wkm_get_globals(s);

    var slot:word := stack_get_val(old_stack, old_esp);
    var ret:word := stack_get_val(new_stack, old_esp);
    if(ret == TRUE)
    {
        assert ffi_usbtd_copy_from_user_copied_some_new_usbtd(old_globals, new_globals, slot);
        Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem(old_globals, new_globals, slot);
        Lemma_ffi_usbtd_copy_from_user_DoNotModifyOtherGlobalVariables(s, r, new_regs, new_stack, new_globals);

        reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
        reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
        reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
        reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

        reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
        reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
        reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
        reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

        forall i | usbtd_map_valid_slot_id(i) && 
                TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
                (usbtd_map_get_type(new_globals, i) == USBTDs_TYPE_QTD32)
            ensures WK_USBTD_Map_SecureGlobalVarValues_qTD32(new_globals, i)
        {
            var new_usbtd_flags := usbtd_map_get_flags(new_globals, i);
            var new_usbtd_types := usbtd_map_get_type(new_globals, i);
            var old_usbtd_flags := usbtd_map_get_flags(old_globals, i);
            var old_usbtd_types := usbtd_map_get_type(old_globals, i);

            assert new_usbtd_flags == old_usbtd_flags;
            assert new_usbtd_types == old_usbtd_types;

            assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(old_globals, i);

            // Prove i != slot
            if (i == slot)
            {
                assert usbtd_map_get_flags(old_globals, slot) == 0;
                assert usbtd_map_get_flags(new_globals, slot) == 0;
                Lemma_TestBit_ReturnFalseIfANumberIs0();
                assert TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) == false;
                assert false;
            }
            assert i != slot;

            Lemma_usbtd_equal_ProveEquivilant(old_globals, new_globals, i);
            assert p_usbtd_equal(old_globals, new_globals, i);

            Lemma_TestBit_ReturnFalseIfANumberIs0();
            Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(old_globals, new_globals, i);
            assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(new_globals, i);
        }

        forall i | usbtd_map_valid_slot_id(i) && 
                TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
                (usbtd_map_get_type(new_globals, i) == USBTDs_TYPE_QH32)
            ensures WK_USBTD_Map_SecureGlobalVarValues_qh32(new_globals, i)
        {
            var new_usbtd_flags := usbtd_map_get_flags(new_globals, i);
            var new_usbtd_types := usbtd_map_get_type(new_globals, i);
            var old_usbtd_flags := usbtd_map_get_flags(old_globals, i);
            var old_usbtd_types := usbtd_map_get_type(old_globals, i);

            assert new_usbtd_flags == old_usbtd_flags;
            assert new_usbtd_types == old_usbtd_types;

            // Prove i != slot
            if (i == slot)
            {
                assert usbtd_map_get_flags(old_globals, slot) == 0;
                assert usbtd_map_get_flags(new_globals, slot) == 0;
                Lemma_TestBit_ReturnFalseIfANumberIs0();
                assert TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) == false;
                assert false;
            }
            assert i != slot;

            Lemma_usbtd_equal_ProveEquivilant(old_globals, new_globals, i);
            assert p_usbtd_equal(old_globals, new_globals, i);

            Lemma_TestBit_ReturnFalseIfANumberIs0();
            Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(old_globals, new_globals, i);
            assert WK_USBTD_Map_SecureGlobalVarValues_qh32(old_globals, i);
        }
    }
}




/*********************** Lemma for <g_usbtd_map_mem> backup, restore and clear ********************/
// Lemma: When restoring a USB TD from the g_temp_usbtd, the result global variable must satisfy 
// WK_USBTD_Map_ValidGlobalVarValues
lemma Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfRestoreUSBTDFromTempTD(
    s:state, s':state, usbtd_slot_id:uint32
)
    requires ValidState(s)

    requires var globals' := wkm_get_globals(s'.wk_mstate);
             WK_ValidGlobalVars_Decls(globals')
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)

    requires var globals1 := wkm_get_globals(s.wk_mstate);
             var globals2 := wkm_get_globals(s'.wk_mstate);
            global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs())
        // Requirement: <g_existing_pids> is unchanged
    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid
    requires var globals1 := wkm_get_globals(s.wk_mstate);
            usbtd_temp_valid_id(globals1) &&
            usbtd_temp_valid_pid(globals1) &&
            usbtd_temp_valid_type(globals1) &&
            usbtd_temp_valid_busid(globals1) &&
            usbtd_temp_valid_wimpdrv_slotid(globals1) &&
            usbtd_temp_valid_usbpdev_slotid(globals1)
        // Requirement: g_temp_usbtd is good
    requires var globals1 := wkm_get_globals(s.wk_mstate);
            forall i :: usbtd_map_valid_slot_id(i) && i != usbtd_slot_id &&
                usbtd_map_get_idword(globals1, i) != USBTD_ID_INVALID
            ==> usbtd_map_get_idword(globals1, i) != usbtd_temp_get_id(globals1)
        // Requirement: No duplicate USBTD ID after restore 

    requires var globals1 := wkm_get_globals(s.wk_mstate);
             var globals2 := wkm_get_globals(s'.wk_mstate);
             ffi_usbtd_restore_stack_and_globals_inner(globals1, globals2, usbtd_slot_id)

    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged

    requires var globals1 := wkm_get_globals(s.wk_mstate);
             WK_USBTD_Map_ValidGlobalVarValues(globals1)

    ensures var globals2 := wkm_get_globals(s'.wk_mstate);
            WK_USBTD_Map_ValidGlobalVarValues(globals2)
{
    reveal ffi_usbtd_restore_stack_and_globals_inner();
    reveal p_usbtd_equal();

    var globals1 := wkm_get_globals(s.wk_mstate);
    var globals2 := wkm_get_globals(s'.wk_mstate);

    var new_id := usbtd_temp_get_id(globals1);
    var new_pid := usbtd_temp_get_pid(globals1).v;
    var new_type := usbtd_temp_get_type(globals1);
    var new_busid := usbtd_temp_get_busid_word(globals1);
    var new_wimpdrv_slot := usbtd_temp_get_wimpdrv_slotid(globals1);
    var new_usbpdev_slot := usbtd_temp_get_usbpdev_slotid(globals1);

    // ID
    var id_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset;
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_idword(globals2, i) <= usbtd_id_counter_read(globals2) ||
                usbtd_map_get_idword(globals2, i) == USBTD_ID_INVALID
    {
        assert usbtd_id_counter_read(globals1) == usbtd_id_counter_read(globals2);
        assert usbtd_slot_valid_id(globals1, i);

        var old_id_i := usbtd_map_get_idword(globals1, i);
        var new_id_i := usbtd_map_get_idword(globals2, i);
        var cur_id_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset;

        assert usbtd_slot_valid_pid(globals1, i);
        if(cur_id_vaddr != id_vaddr)
        {
            assert old_id_i == new_id_i;
        }
        else
        {
            assert new_id_i == new_id;
        }
    }

    // PID
    var pid_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset;
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures (usbtd_map_get_pid(globals2, i) == WS_PartitionID(PID_INVALID) || 
            usbtd_map_get_pid(globals2, i) in pids_parse_g_wimp_pids(globals2))
    {
        var old_pid_i := usbtd_map_get_pid(globals1, i);
        var new_pid_i := usbtd_map_get_pid(globals2, i);
        var cur_pid_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset;

        assert usbtd_slot_valid_pid(globals1, i);
        if(cur_pid_vaddr != pid_vaddr)
        {
            assert old_pid_i == new_pid_i;
        }
        else
        {
            assert new_pid_i.v == new_pid;
        }
    }

    // Type
    var type_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset;
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_type(globals2, i)
    {
        var old_type_i := usbtd_map_get_type(globals1, i);
        var new_type_i := usbtd_map_get_type(globals2, i);
        var cur_type_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset;

        assert usbtd_slot_valid_type(globals1, i);
        if(cur_type_vaddr != type_vaddr)
        {
            assert old_type_i == new_type_i;
        }
        else
        {
            assert new_type_i == new_type;
        }
    }

    // Bus ID
    var busid_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset;
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_busid(globals2, i)
    {
        var old_busid_i := usbtd_map_get_busid(globals1, i);
        var new_busid_i := usbtd_map_get_busid(globals2, i);
        var cur_busid_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset;

        assert usbtd_slot_valid_type(globals1, i);
        if(cur_busid_vaddr != busid_vaddr)
        {
            assert old_busid_i == new_busid_i;
        }
        else
        {
            assert new_busid_i == new_busid;
        }
    }

    // WimpDrv Slot ID
    var wimpdrv_slot_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_wimpdrv_slotid(globals2, i)
    {
        var old_slotid_i := usbtd_map_get_wimpdrv_slotid(globals1, i);
        var new_slotid_i := usbtd_map_get_wimpdrv_slotid(globals2, i);
        var cur_busid_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;

        assert usbtd_slot_valid_type(globals1, i);
        if(cur_busid_vaddr != wimpdrv_slot_vaddr)
        {
            assert old_slotid_i == new_slotid_i;
            assert usbtd_slot_valid_wimpdrv_slotid(globals1, i);
            assert usbtd_slot_valid_wimpdrv_slotid(globals2, i);
        }
        else
        {
            assert new_slotid_i == new_wimpdrv_slot;
            assert usbtd_slot_valid_wimpdrv_slotid(globals2, i);
        }
    }

    // USBPDev Slot ID
    var usbpdev_slot_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_usbpdev_slotid(globals2, i)
    {
        var old_slotid_i := usbtd_map_get_usbpdev_slotid(globals1, i);
        var new_slotid_i := usbtd_map_get_usbpdev_slotid(globals2, i);
        var cur_busid_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;

        assert usbtd_slot_valid_type(globals1, i);
        if(cur_busid_vaddr != usbpdev_slot_vaddr)
        {
            assert old_slotid_i == new_slotid_i;
            assert usbtd_slot_valid_usbpdev_slotid(globals1, i);
            assert usbtd_slot_valid_usbpdev_slotid(globals2, i);
        }
        else
        {
            assert new_slotid_i == new_usbpdev_slot;
            assert usbtd_slot_valid_usbpdev_slotid(globals2, i);
        }
    }

    Lemma_ValidState_ImpliesWK_ValidGlobalVarValues_ActiveUSBTDs(s'.subjects, s'.objects, s'.id_mappings, globals2);
    reveal WK_ValidGlobalVarValues_ActiveUSBTDs();
}

// Lemma: ffi_usbtd_restore ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_usbtd_restore_ResultStateIsValidMState(
    s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires ValidState(s)
    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_Restore_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, 0)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
            ins_valid_usbtd_restore(wkm_stack_get_all(s.wk_mstate), wkm_get_globals(s.wk_mstate), old_esp)

    requires ffi_usbtd_restore_stack_and_globals(s.wk_mstate, new_globals)

    ensures WK_ValidMState(r.wk_mstate)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_restore_stack_and_globals_inner();

    var s_wkm := s.wk_mstate;
    var r_wkm := r.wk_mstate;

    var old_esp := x86_get_reg(s_wkm, ESP);
    var old_stack := wkm_stack_get_all(s_wkm);
    var old_globals := wkm_get_globals(s_wkm);

    var slot:word := stack_get_val(old_stack, old_esp);

    lemma_DistinctGlobals();

    assert global_read_fullval(old_globals, G_Existing_PIDs()) == global_read_fullval(new_globals, G_Existing_PIDs());

    Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGExistingPIDsAndPIDCounterUnchanged(old_globals, new_globals);
    Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(old_globals, new_globals);

    Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(old_globals, new_globals);

    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfRestoreUSBTDFromTempTD(s, r, slot);
    Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(old_globals, new_globals);
    Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfRestoreUSBTDFromTempTD(old_globals, new_globals, slot);
    assert WK_ValidMState(r_wkm);
}

// Lemma: ffi_usbtd_restore ends up at a result state fulfilling ValidState
lemma Lemma_ffi_usbtd_restore_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_Restore_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, 0)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
            ins_valid_usbtd_restore(wkm_stack_get_all(s.wk_mstate), wkm_get_globals(s.wk_mstate), old_esp)

    requires ffi_usbtd_restore_stack_and_globals(s.wk_mstate, new_globals)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_restore_stack_and_globals_inner();

    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s,r);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    
    Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(s,r);
    Lemma_WK_ValidGlobalVarValues_USBPDevList_OnWKMStateSubjectsModification_IfUSBPDevListIsUnchanged(s,r);

    Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_PEHCIs_OnSubjsExceptOSDevsModification(s, r);
}

lemma Lemma_ffi_usbtd_backup_stack_and_globals_ImpliesNonScratchpadGlobalVarsUnchanged(old_globals:globalsmap, new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires usbtd_map_valid_slot_id(td_slot)

    requires ffi_usbtd_backup_stack_and_globals_inner(old_globals, new_globals, td_slot)

    ensures global_non_scratchpad_vars_are_unchanged(old_globals, new_globals)
{
    reveal ffi_usbtd_backup_stack_and_globals_inner();
    reveal global_non_scratchpad_vars_are_unchanged();

    assert globals_other_gvar_unchanged(old_globals, new_globals, G_Temp_USBTD());

    assert global_non_scratchpad_vars_are_unchanged(old_globals, new_globals);
}

lemma Lemma_ffi_usbtd_backup_ProveSecurityProperty_WK_USBTD_Map_SecureGlobalVarValues(old_globals:globalsmap, new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(old_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(old_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(new_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(new_globals)
    requires usbtd_map_valid_slot_id(td_slot)

    requires ffi_usbtd_backup_stack_and_globals_inner(old_globals, new_globals, td_slot)

    requires WK_USBTD_Map_SecureGlobalVarValues(old_globals)

    ensures WK_USBTD_Map_SecureGlobalVarValues(new_globals)
{
    reveal global_non_scratchpad_vars_are_unchanged();

    Lemma_ffi_usbtd_backup_stack_and_globals_ImpliesNonScratchpadGlobalVarsUnchanged(old_globals, new_globals, td_slot);
    Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(old_globals, new_globals);
}

lemma Lemma_ffi_usbtd_backup_stack_and_globals_ImpliesIDOfUSBTDIsWrittenInTempUSBTD(old_globals:globalsmap, new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires usbtd_map_valid_slot_id(td_slot)

    requires ffi_usbtd_backup_stack_and_globals_inner(old_globals, new_globals, td_slot)

    ensures usbtd_map_get_idword(old_globals, td_slot) == usbtd_temp_get_id(new_globals)
{
    reveal ffi_usbtd_backup_stack_and_globals_inner();
    reveal global_non_scratchpad_vars_are_unchanged();
}

lemma Lemma_ffi_usbtd_backup_stack_and_globals_ImpliesPIDOfUSBTDIsWrittenInTempUSBTD(old_globals:globalsmap, new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires usbtd_map_valid_slot_id(td_slot)

    requires ffi_usbtd_backup_stack_and_globals_inner(old_globals, new_globals, td_slot)

    ensures usbtd_map_get_pid(old_globals, td_slot) == usbtd_temp_get_pid(new_globals)
{
    reveal ffi_usbtd_backup_stack_and_globals_inner();
    reveal global_non_scratchpad_vars_are_unchanged();
}

lemma Lemma_ffi_usbtd_backup_stack_and_globals_PreserveUSBTDFlags(old_globals:globalsmap, new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires usbtd_map_valid_slot_id(td_slot)
    
    requires ffi_usbtd_backup_stack_and_globals_inner(old_globals, new_globals, td_slot)

    ensures usbtd_map_get_flags(new_globals, td_slot) == usbtd_map_get_flags(old_globals, td_slot)
{
    reveal ffi_usbtd_backup_stack_and_globals_inner();
    reveal global_non_scratchpad_vars_are_unchanged();
}

lemma Lemma_ffi_usbtd_backup_stack_and_globals_PreserveUSBTDType(old_globals:globalsmap, new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires usbtd_map_valid_slot_id(td_slot)
    
    requires ffi_usbtd_backup_stack_and_globals_inner(old_globals, new_globals, td_slot)

    ensures usbtd_map_get_type(new_globals, td_slot) == usbtd_map_get_type(old_globals, td_slot)
{
    reveal ffi_usbtd_backup_stack_and_globals_inner();
    reveal global_non_scratchpad_vars_are_unchanged();
}


lemma Lemma_ffi_usbtd_backup_stack_and_globals_ProveTempUSBTDFlagsIsEmpty(old_globals:globalsmap, new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires usbtd_map_valid_slot_id(td_slot)

    requires usbtd_map_get_flags(old_globals, td_slot) == 0
    requires ffi_usbtd_backup_stack_and_globals_inner(old_globals, new_globals, td_slot)

    ensures usbtd_temp_get_flags(new_globals) == 0
{
    reveal ffi_usbtd_backup_stack_and_globals_inner();
    reveal global_non_scratchpad_vars_are_unchanged();
}

// Lemma: If <ffi_usbtd_backup_stack_and_globals_inner>, then g_temp_usbtd is good
lemma Lemma_ffi_usbtd_backup_stack_and_globals_inner_TempUSBTDMustBeValid(globals1:globalsmap, globals2:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires usbtd_map_valid_slot_id(td_slot)

    requires ffi_usbtd_backup_stack_and_globals_inner(globals1, globals2, td_slot)

    ensures usbtd_temp_valid_id(globals2)
    ensures usbtd_temp_valid_pid(globals2)
    ensures usbtd_temp_valid_type(globals2)
    ensures usbtd_temp_valid_busid(globals2)
    ensures usbtd_temp_valid_wimpdrv_slotid(globals2)
    ensures usbtd_temp_valid_usbpdev_slotid(globals2)

    ensures forall i :: usbtd_map_valid_slot_id(i) && i != td_slot &&
                usbtd_map_get_idword(globals2, i) != USBTD_ID_INVALID
            ==> usbtd_map_get_idword(globals2, i) != usbtd_temp_get_id(globals2)
{
    reveal ffi_usbtd_backup_stack_and_globals_inner();

    // Prove usbtd_temp_valid_id(globals2)
    assert global_read_fullval(globals1, G_USBTD_ID_Counter()) == global_read_fullval(globals2, G_USBTD_ID_Counter());
    assert usbtd_map_get_idword(globals1, td_slot) == usbtd_temp_get_id(globals2);
    assert usbtd_slot_valid_id(globals1, td_slot);

    // Prove usbtd_temp_valid_pid
    assert global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs());

    var pid_temp := usbtd_temp_get_pid(globals2);
    var pid := usbtd_map_get_pid(globals1, td_slot);
    assert pid_temp == pid;
    assert usbtd_slot_valid_pid(globals1, td_slot);
     
    assert (pid_temp == WS_PartitionID(PID_INVALID) || pid_temp in pids_parse_g_wimp_pids(globals2));

    // Prove usbtd_temp_valid_type
    assert usbtd_slot_valid_type(globals1, td_slot);

    // Prove usbtd_temp_valid_busid
    assert usbtd_slot_valid_busid(globals1, td_slot);

    // Prove usbtd_temp_valid_wimpdrv_slotid
    assert usbtd_slot_valid_wimpdrv_slotid(globals1, td_slot);

    // Prove usbtd_temp_valid_usbpdev_slotid
    assert usbtd_slot_valid_usbpdev_slotid(globals1, td_slot);
}

// Lemma: If globals1 == globals2, then global_non_scratchpad_vars_are_unchanged(globals1, globals2)
lemma Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires globals1 == globals2
    
    ensures global_non_scratchpad_vars_are_unchanged(globals1, globals2)
{
    reveal global_non_scratchpad_vars_are_unchanged();
}

// Lemma: ffi_usbtd_backup ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_usbtd_backup_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_Backup_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, 0)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
            var old_stack := wkm_stack_get_all(s);
            var td_slot:word := stack_get_val(old_stack, old_esp); 
            usbtd_map_valid_slot_id(td_slot) 

    requires ffi_usbtd_backup_stack_and_globals(s, new_globals)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_backup_stack_and_globals_inner();

    var old_esp := x86_get_reg(s, ESP);
    var old_stack := wkm_stack_get_all(s);
    var old_globals := wkm_get_globals(s);

    var slot:word := stack_get_val(old_stack, old_esp);

    Lemma_ffi_usbtd_backup_stack_and_globals_ImpliesNonScratchpadGlobalVarsUnchanged(old_globals, new_globals, slot);
    assert global_non_scratchpad_vars_are_unchanged(old_globals, new_globals);

    Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGExistingPIDsAndPIDCounterUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(wkm_get_globals(s), wkm_get_globals(r));
    assert WK_ValidMState(r);
}

// Lemma: ffi_usbtd_backup ends up at a result state fulfilling ValidState
lemma Lemma_ffi_usbtd_backup_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_Backup_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, 0)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
            var old_stack := wkm_stack_get_all(s.wk_mstate);
            var td_slot:word := stack_get_val(old_stack, old_esp); 
            usbtd_map_valid_slot_id(td_slot) 

    requires ffi_usbtd_backup_stack_and_globals(s.wk_mstate, new_globals)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_backup_stack_and_globals_inner();

    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s,r);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    
    Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(s,r);
    Lemma_WK_ValidGlobalVarValues_USBPDevList_OnWKMStateSubjectsModification_IfUSBPDevListIsUnchanged(s,r);

    Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_PEHCIs_OnSubjsExceptOSDevsModification(s, r);
}

// Lemma: Restoring USB TD after backing up the USB TD (only the USB TD is modified in between), then all global
// variables except G_Temp_* are unmodified
lemma Lemma_USBTD_BackupAndRestore_ResultsInOriginalNonScratchpadGlobalVars(
    globals1:globalsmap, globals2:globalsmap, globals3:globalsmap, globals4:globalsmap, usbtd_slot_id:uint32
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(globals3)
    requires WK_ValidGlobalVars_Decls(globals4)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid

    requires ffi_usbtd_backup_stack_and_globals_inner(globals1, globals2, usbtd_slot_id)
    requires usbtd_map_modify_one_usbtd_only(globals2, globals3, usbtd_slot_id)
    requires ffi_usbtd_restore_stack_and_globals_inner(globals3, globals4, usbtd_slot_id)
        // Requirement: Backup first, then with the same global variable, restore the USB TD

    ensures global_non_scratchpad_vars_are_unchanged(globals1, globals4)
{
    reveal ffi_usbtd_backup_stack_and_globals_inner();
    reveal ffi_usbtd_restore_stack_and_globals_inner();
    reveal global_non_scratchpad_vars_are_unchanged();
    reveal p_usbtd_content_equal();
    reveal p_usbtd_equal();
    
    // Prove global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals4, G_USBTD_MAP_MEM());
    assert usbtd_map_get_inputparam(globals1, usbtd_slot_id, G_USBTDs_MAP_ENTRY_InputParam1) == usbtd_temp_get_inputparam(globals3, G_USBTDs_MAP_ENTRY_InputParam1) &&
                usbtd_map_get_inputparam(globals1, usbtd_slot_id, G_USBTDs_MAP_ENTRY_InputParam2) == usbtd_temp_get_inputparam(globals3, G_USBTDs_MAP_ENTRY_InputParam2) &&
                usbtd_map_get_inputparam(globals1, usbtd_slot_id, G_USBTDs_MAP_ENTRY_InputParam3) == usbtd_temp_get_inputparam(globals3, G_USBTDs_MAP_ENTRY_InputParam3);

    assert p_usbtd_equal(globals1, globals4, usbtd_slot_id);


    // Prove other USB TDs are unmodified
    forall i:uint32 | usbtd_map_valid_slot_id(i) && i != usbtd_slot_id
        ensures p_usbtd_equal(globals1, globals4, i)
    {
        assert p_usbtd_content_equal(globals1, globals2, i);
        assert p_usbtd_content_equal(globals2, globals4, i);
    }

    Lemma_USBTD_Map_MEM_IfAllUSBTDSlotsEqual_ThenEntireMemEqual(globals1, globals4);
    assert global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals4, G_USBTD_MAP_MEM());
}

// Lemma: CALL_USBTD_IsRefTargetUSBTD ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_usbtd_is_ref_target_usbtd_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_IsRefTargetUSBTD_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_USBTD_IsRefTargetUSBTD_ReturnWords)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    assert wkm_get_globals(s) == wkm_get_globals(r);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s,r);
}

// Lemma: CALL_USBTD_IsRefTargetUSBTD ends up at a result state fulfilling ValidState
lemma Lemma_ffi_usbtd_is_ref_target_usbtd_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_IsRefTargetUSBTD_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input params take one words, output params take four words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_USBTD_IsRefTargetUSBTD_ReturnWords)

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

// Lemma: ffi_usbtd_clear_content ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_usbtd_clear_content_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_Clear_Content_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, 0)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
            var old_stack := wkm_stack_get_all(s);
            var td_slot:word := stack_get_val(old_stack, old_esp); 
            usbtd_map_valid_slot_id(td_slot) 

    requires var old_esp := x86_get_reg(s, ESP);
            ins_valid_usbtd_clear_content(wkm_stack_get_all(s), wkm_get_globals(s), old_esp)

    requires ffi_usbtd_clear_content_stack_and_globals(s, new_globals)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_clear_content_stack_and_globals_qtd32();
    reveal ffi_usbtd_clear_content_stack_and_globals_qh32();
    reveal p_usbtd_equal();

    var old_esp := x86_get_reg(s, ESP);
    var old_stack := wkm_stack_get_all(s);
    var old_globals := wkm_get_globals(s);

    var slot:word := stack_get_val(old_stack, old_esp);

    lemma_DistinctGlobals();

    assert global_read_fullval(old_globals, G_Existing_PIDs()) == global_read_fullval(new_globals, G_Existing_PIDs());

    Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGExistingPIDsAndPIDCounterUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_ffi_usbtd_clear_content_PreserveOtherFieldsInUSBTDMem(s, old_globals, new_globals, slot);
    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfPIDTypeBusIDWimpDrvSlotIDUSBPDevSlotID_FieldsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfClearUSBTD(wkm_get_globals(s), wkm_get_globals(r), slot);

    assert WK_ValidMState(r);
}

// Lemma: ffi_usbtd_clear_content ends up at a result state fulfilling ValidState
lemma Lemma_ffi_usbtd_clear_content_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack, globals := new_globals))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_Clear_Content_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, 0)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
            var old_stack := wkm_stack_get_all(s.wk_mstate);
            var td_slot:word := stack_get_val(old_stack, old_esp); 
            usbtd_map_valid_slot_id(td_slot) 

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
            ins_valid_usbtd_clear_content(wkm_stack_get_all(s.wk_mstate), wkm_get_globals(s.wk_mstate), old_esp)

    requires ffi_usbtd_clear_content_stack_and_globals(s.wk_mstate, new_globals)

    ensures ValidState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_clear_content_stack_and_globals_qtd32();
    reveal ffi_usbtd_clear_content_stack_and_globals_qh32();
    reveal p_usbtd_equal();

    // Prove WSM_SubjPID of subjects are unchanged
    Lemma_SubjPIDs_ValuesAreUnchanged_IfOSSubjsAreUnchanged_AndWimpSubjsIDWordsAndFlagsAndRecordedPIDsAreUnchanged(s,r);

    Lemma_WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    
    Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(s,r);
    Lemma_WK_ValidGlobalVarValues_USBPDevList_OnWKMStateSubjectsModification_IfUSBPDevListIsUnchanged(s,r);

    Lemma_WK_ValidState_DevsActivateCond_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s,r);
    Lemma_WK_ValidObjsAddrs_PEHCIs_OnSubjsExceptOSDevsModification(s, r);
}

// Lemma: if <ffi_usbtd_clear_content_stack_and_globals> is true, then other fields in <g_usbtd_mem_map> is unmodified
lemma Lemma_ffi_usbtd_clear_content_PreserveOtherFieldsInUSBTDMem(old_wkm:WK_MState, old_globals:globalsmap, new_globals:globalsmap, slot:uint32)
    requires WK_ValidMState(old_wkm)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
             var stack_params_space := FFI_USBTD_Clear_Content_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires var old_esp := x86_get_reg(old_wkm, ESP); 
            ins_valid_usbtd_clear_content(wkm_stack_get_all(old_wkm), wkm_get_globals(old_wkm), old_esp)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires var old_esp := x86_get_reg(old_wkm, ESP);
            var old_stack := wkm_stack_get_all(old_wkm);
            var td_slot:word := stack_get_val(old_stack, old_esp); 
            usbtd_map_valid_slot_id(td_slot) &&
            td_slot == slot
    requires old_globals == wkm_get_globals(old_wkm)

    requires ffi_usbtd_clear_content_stack_and_globals(old_wkm, new_globals)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM && i != slot ==> p_usbtd_content_equal(old_globals, new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_idword(old_globals, i) == usbtd_map_get_idword(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_pid(old_globals, i) == usbtd_map_get_pid(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_type(old_globals, i) == usbtd_map_get_type(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_busid_word(old_globals, i) == usbtd_map_get_busid_word(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_flags(old_globals, i) == usbtd_map_get_flags(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_wimpdrv_slotid(old_globals, i) == usbtd_map_get_wimpdrv_slotid(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_usbpdev_slotid(old_globals, i) == usbtd_map_get_usbpdev_slotid(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_handle(old_globals, i) == usbtd_map_get_handle(new_globals, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_inputparam(old_globals, i, G_USBTDs_MAP_ENTRY_InputParam1) == usbtd_map_get_inputparam(new_globals, i, G_USBTDs_MAP_ENTRY_InputParam1)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_inputparam(old_globals, i, G_USBTDs_MAP_ENTRY_InputParam2) == usbtd_map_get_inputparam(new_globals, i, G_USBTDs_MAP_ENTRY_InputParam2)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_inputparam(old_globals, i, G_USBTDs_MAP_ENTRY_InputParam3) == usbtd_map_get_inputparam(new_globals, i, G_USBTDs_MAP_ENTRY_InputParam3)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures i != slot ==> p_usbtd_content_equal(old_globals, new_globals, i)
        ensures usbtd_map_get_idword(old_globals, i) == usbtd_map_get_idword(new_globals, i)
        ensures usbtd_map_get_pid(old_globals, i) == usbtd_map_get_pid(new_globals, i)
        ensures usbtd_map_get_type(old_globals, i) == usbtd_map_get_type(new_globals, i)
        ensures usbtd_map_get_busid_word(old_globals, i) == usbtd_map_get_busid_word(new_globals, i)
        ensures usbtd_map_get_flags(old_globals, i) == usbtd_map_get_flags(new_globals, i)
        ensures usbtd_map_get_wimpdrv_slotid(old_globals, i) == usbtd_map_get_wimpdrv_slotid(new_globals, i)
        ensures usbtd_map_get_usbpdev_slotid(old_globals, i) == usbtd_map_get_usbpdev_slotid(new_globals, i)
        ensures usbtd_map_get_inputparam(old_globals, i, G_USBTDs_MAP_ENTRY_InputParam1) == usbtd_map_get_inputparam(new_globals, i, G_USBTDs_MAP_ENTRY_InputParam1)
        ensures usbtd_map_get_inputparam(old_globals, i, G_USBTDs_MAP_ENTRY_InputParam2) == usbtd_map_get_inputparam(new_globals, i, G_USBTDs_MAP_ENTRY_InputParam2)
        ensures usbtd_map_get_inputparam(old_globals, i, G_USBTDs_MAP_ENTRY_InputParam3) == usbtd_map_get_inputparam(new_globals, i, G_USBTDs_MAP_ENTRY_InputParam3)
    {
        if(i == slot)
        {
            assert usbtd_map_get_pid(old_globals, i) == usbtd_map_get_pid(new_globals, i);
            assert usbtd_map_get_type(old_globals, i) == usbtd_map_get_type(new_globals, i);
            assert usbtd_map_get_busid_word(old_globals, i) == usbtd_map_get_busid_word(new_globals, i);
            assert usbtd_map_get_flags(old_globals, i) == usbtd_map_get_flags(new_globals, i);
            assert usbtd_map_get_inputparam(old_globals, i, G_USBTDs_MAP_ENTRY_InputParam1) == usbtd_map_get_inputparam(new_globals, i, G_USBTDs_MAP_ENTRY_InputParam1);
            assert usbtd_map_get_inputparam(old_globals, i, G_USBTDs_MAP_ENTRY_InputParam2) == usbtd_map_get_inputparam(new_globals, i, G_USBTDs_MAP_ENTRY_InputParam2);
            assert usbtd_map_get_inputparam(old_globals, i, G_USBTDs_MAP_ENTRY_InputParam3) == usbtd_map_get_inputparam(new_globals, i, G_USBTDs_MAP_ENTRY_InputParam3);
        }
        else
        {
            assert p_usbtd_equal(old_globals, new_globals, i);
        }
    }
}

// Lemma: CALL_USBTD_Clear_Content does not modify other global variables
lemma Lemma_ffi_usbtd_clear_content_DoNotModifyOtherGlobalVariables(
    s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_Clear_Content_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, 0)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires var old_esp := x86_get_reg(s, ESP); 
            ins_valid_usbtd_clear_content(wkm_stack_get_all(s), wkm_get_globals(s), old_esp)
    requires ffi_usbtd_clear_content_stack_and_globals(s, new_globals)
        // Requirement: <ffi_usbtd_clear_content> transits states correctly

    ensures globals_other_gvar_unchanged(wkm_get_globals(s), wkm_get_globals(r), G_USBTD_MAP_MEM())
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_copy_from_user_stack_and_globals();
    reveal ffi_usbtd_copy_from_user_copied_some_new_usbtd();
}

// Lemma: <ffi_usbtd_clear_content> satisfies the security property <WK_USBTD_Map_SecureGlobalVarValues>
lemma Lemma_ffi_usbtd_clear_content_ProveSecurityProperty_WK_USBTD_Map_SecureGlobalVarValues(
    s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_Clear_Content_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, 0)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires var old_esp := x86_get_reg(s, ESP); 
            ins_valid_usbtd_clear_content(wkm_stack_get_all(s), wkm_get_globals(s), old_esp)
    requires ffi_usbtd_clear_content_stack_and_globals(s, new_globals)
        // Requirement: <ffi_usbtd_clear_content> transits states correctly

    requires WK_USBTD_Map_ValidGlobalVarValues(new_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(new_globals)
    requires WK_USBTD_Map_SecureGlobalVarValues(wkm_get_globals(s))

    ensures WK_USBTD_Map_SecureGlobalVarValues(new_globals) 
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    var old_esp := x86_get_reg(s, ESP);
    var old_stack := wkm_stack_get_all(s);
    var old_globals := wkm_get_globals(s);

    var slot:word := stack_get_val(old_stack, old_esp);

    Lemma_ffi_usbtd_clear_content_PreserveOtherFieldsInUSBTDMem(s, old_globals, new_globals, slot);
    Lemma_ffi_usbtd_clear_content_DoNotModifyOtherGlobalVariables(s, r, new_regs, new_stack, new_globals);

    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    forall i | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(new_globals, i) == USBTDs_TYPE_QTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qTD32(new_globals, i)
    {
        var new_usbtd_flags := usbtd_map_get_flags(new_globals, i);
        var new_usbtd_types := usbtd_map_get_type(new_globals, i);
        var old_usbtd_flags := usbtd_map_get_flags(old_globals, i);
        var old_usbtd_types := usbtd_map_get_type(old_globals, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;

        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(old_globals, i);

        // Prove i != slot
        if (i == slot)
        {
            assert usbtd_map_get_flags(old_globals, slot) == 0;
            assert usbtd_map_get_flags(new_globals, slot) == 0;
            Lemma_TestBit_ReturnFalseIfANumberIs0();
            assert TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) == false;
            assert false;
        }
        assert i != slot;

        Lemma_usbtd_equal_ProveEquivilant(old_globals, new_globals, i);
        assert p_usbtd_equal(old_globals, new_globals, i);

        Lemma_TestBit_ReturnFalseIfANumberIs0();
        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(old_globals, new_globals, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(new_globals, i);
    }

    forall i | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(new_globals, i) == USBTDs_TYPE_QH32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qh32(new_globals, i)
    {
        var new_usbtd_flags := usbtd_map_get_flags(new_globals, i);
        var new_usbtd_types := usbtd_map_get_type(new_globals, i);
        var old_usbtd_flags := usbtd_map_get_flags(old_globals, i);
        var old_usbtd_types := usbtd_map_get_type(old_globals, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;

        // Prove i != slot
        if (i == slot)
        {
            assert usbtd_map_get_flags(old_globals, slot) == 0;
            assert usbtd_map_get_flags(new_globals, slot) == 0;
            Lemma_TestBit_ReturnFalseIfANumberIs0();
            assert TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) == false;
            assert false;
        }
        assert i != slot;

        Lemma_usbtd_equal_ProveEquivilant(old_globals, new_globals, i);
        assert p_usbtd_equal(old_globals, new_globals, i);

        Lemma_TestBit_ReturnFalseIfANumberIs0();
        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(old_globals, new_globals, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_qh32(old_globals, i);
    }
}

// Lemma: CALL_USBTD_Clear_Content ends up at a result state fulfilling WK_ValidMState and WK_EEHCI_Mem_SecureGlobalVarValues
lemma Lemma_ffi_usbtd_clear_content_ResultStateIsValidMState_AndEEHCIMemSecureState(
    s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap, new_globals:globalsmap
)
    requires WK_ValidMState(s)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(wkm_get_globals(s))
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2.(globals := new_globals)

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_Clear_Content_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // Input param takes two words, output param takes one words, <stack_params_space> = max(input_params, 
                // output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, 0)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires var old_esp := x86_get_reg(s, ESP); 
            ins_valid_usbtd_clear_content(wkm_stack_get_all(s), wkm_get_globals(s), old_esp)
    requires ffi_usbtd_clear_content_stack_and_globals(s, new_globals)
        // Requirement: <ffi_usbtd_clear_content> transits states correctly

    ensures WK_ValidMState(r)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(wkm_get_globals(r))
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();
    reveal ffi_usbtd_copy_from_user_stack_and_globals();
    reveal ffi_usbtd_copy_from_user_copied_some_new_usbtd();

    var old_esp := x86_get_reg(s, ESP);
    var old_stack := wkm_stack_get_all(s);
    var old_globals := wkm_get_globals(s);

    var slot:word := stack_get_val(old_stack, old_esp);

    Lemma_ffi_usbtd_clear_content_PreserveOtherFieldsInUSBTDMem(s, old_globals, new_globals, slot);
    assert global_read_fullval(old_globals, G_Existing_PIDs()) == global_read_fullval(new_globals, G_Existing_PIDs());

    Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGExistingPIDsAndPIDCounterUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(wkm_get_globals(s), wkm_get_globals(r));

    Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(wkm_get_globals(s), wkm_get_globals(r));
    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(wkm_get_globals(s), wkm_get_globals(r));
    assert WK_ValidMState(r);
}

// Lemma: CALL_USBTD_CheckNotModifyUSBPDevAddrs ends up at a result state fulfilling WK_ValidMState
lemma Lemma_ffi_usbtd_check_not_modify_usbpdev_addrs_ResultStateIsValidMState(s:WK_MState, r:WK_MState, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires WK_ValidMState(s)
    requires var s1 := s.(regs := new_regs); 
             var s2 := s1.(m := new_stack);
             r == s2

    requires var old_esp := x86_get_reg(s, ESP);
             var stack_params_space := FFI_USBTD_CheckNotModifyUSBPDevAddrs_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_sp_and_bp(s, new_regs)
    requires ffi_preserve_old_stack(s, new_stack, FFI_USBTD_CheckNotModifyUSBPDevAddrs_ReturnWords)

    ensures WK_ValidMState(r)
{
    reveal ffi_preserve_old_stack();
    reveal x86wk_valid_memstate();
    reveal ffi_preserve_sp_and_bp();

    assert wkm_get_globals(s) == wkm_get_globals(r);
    Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(s,r);
}

// Lemma: CALL_USBTD_CheckNotModifyUSBPDevAddrs ends up at a result state fulfilling ValidState
lemma Lemma_ffi_usbtd_check_not_modify_usbpdev_addrs_ResultStateIsValidState(s:state, r:state, new_regs:map<x86Reg, word>, new_stack:wk_memmap)
    requires ValidState(s)
    requires WK_ValidMState(r.wk_mstate)

    requires r == s.(wk_mstate := s.wk_mstate.(regs := new_regs, m := new_stack))

    requires var old_esp := x86_get_reg(s.wk_mstate, ESP);
             var stack_params_space := FFI_USBTD_CheckNotModifyUSBPDevAddrs_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
                // <stack_params_space> = max(input_params, output_params)
    requires ffi_preserve_sp_and_bp(s.wk_mstate, new_regs)
    requires ffi_preserve_old_stack(s.wk_mstate, new_stack, FFI_USBTD_CheckNotModifyUSBPDevAddrs_ReturnWords)

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




/*********************** Private Lemmas  ********************/
lemma Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem_Individual(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_TD_BytesOffset + MAX_USB_TD_BYTES
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM && i != slot ==> p_usbtd_content_equal(globals1, globals2, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_idword(globals1, i) == usbtd_map_get_idword(globals2, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_pid(globals1, i) == usbtd_map_get_pid(globals2, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_type(globals1, i) == usbtd_map_get_type(globals2, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_busid_word(globals1, i) == usbtd_map_get_busid_word(globals2, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_flags(globals1, i) == usbtd_map_get_flags(globals2, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_wimpdrv_slotid(globals1, i) == usbtd_map_get_wimpdrv_slotid(globals2, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_usbpdev_slotid(globals1, i) == usbtd_map_get_usbpdev_slotid(globals2, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_handle(globals1, i) == usbtd_map_get_handle(globals2, i)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam1) == usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam1)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam2) == usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam2)
    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam3) == usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam3)
{
    Lemma_WK_USB_TD_Map_PropertiesOfTDAddrs(slot);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, offset);

    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot_USBTDContents(globals1, globals2, slot, offset, new_v);
    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals1, globals2, slot, offset, new_v);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals1, globals2, slot, offset, new_v);
    Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals1, globals2, slot, offset, new_v);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals1, globals2, slot, offset, new_v);
    Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals1, globals2, slot, offset, new_v);
    Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(globals1, globals2, slot, offset, new_v);
    Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(globals1, globals2, slot, offset, new_v);

    Lemma_WK_USB_TD_Map_PreserveHandleFieldIfModifyOtherFields(globals1, globals2, slot, offset, new_v);
    Lemma_WK_USB_TD_Map_PreserveInputParam1FieldIfModifyOtherFields(globals1, globals2, slot, offset, new_v);
    Lemma_WK_USB_TD_Map_PreserveInputParam2FieldIfModifyOtherFields(globals1, globals2, slot, offset, new_v);
    Lemma_WK_USB_TD_Map_PreserveInputParam3FieldIfModifyOtherFields(globals1, globals2, slot, offset, new_v);
}