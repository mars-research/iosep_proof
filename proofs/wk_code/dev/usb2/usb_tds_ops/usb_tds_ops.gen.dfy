include "usb_tds_ops_impl.gen.dfy"
include "usb_tds_qtds_ops_impl.gen.dfy"
include "usb_tds_qhs_ops_impl.gen.dfy"
include "..\\..\\..\\transition_constraints.s.dfy"
include "..\\..\\..\\proof\\wkapi_commutative_diagram.i.dfy"
//-- USBTD_slot_allocate_1slot

function method{:opaque} va_code_USBTD_slot_allocate_1slot():va_code
{
  va_Block(va_CCons(va_code_USBTD_slot_allocate_1slot_Impl(), va_CNil()))
}

lemma va_lemma_USBTD_slot_allocate_1slot(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state, out_new_idword:word)
  requires va_require(va_b0, va_code_USBTD_slot_allocate_1slot(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 14 *
    ARCH_WORD_BYTES + 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space)
    && (var stack_retval_space := 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_retval_space))
  requires var td_type:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); ((td_type == USBTDs_TYPE_QTD32 || td_type == USBTDs_TYPE_QH32) || td_type ==
    USBTDs_TYPE_iTD32) || td_type == USBTDs_TYPE_siTD32
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  var td_type:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var new_td_slot:uint32
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var dm :=
    WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_USBTD_Allocate1Slot_CommutativeDiagram_Property(va_s0, dm, dm', out_new_idword, pid, ret)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_USBTD_slot_allocate_1slot();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2, va_ltmp3 := va_lemma_USBTD_slot_allocate_1slot_Impl(va_b1, va_s0, va_sM);
  out_new_idword := va_ltmp3;
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  ghost var td_type:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
    ARCH_WORD_BYTES);
  ghost var pid:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
  ghost var ret:uint32 := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  ghost var new_td_slot:uint32 := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s) +
    ARCH_WORD_BYTES);
  assert InstSaneState(s');  // line 83 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 2 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 85 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_OnUSBTDAllocation(s, s',
    new_td_slot, out_new_idword, td_type, pid, ret);
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_OnUSBTDAllocation(s, s',
    new_td_slot, out_new_idword, td_type, pid, ret);
  assert OpsSaneStateSubset(s');  // line 92 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  if (ret == TRUE)
  {
    ghost var dm := WSM_MapSecureState(s);
    Lemma_USBTD_Allocate1Slot_ProveCommutativeDiagram_ProvePreCondition(s, out_new_idword);
    Lemma_USBTD_Allocate1Slot_ProveCommutativeDiagram(s, dm, new_td_slot, out_new_idword, td_type,
      pid, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_USBTD_Allocate1Slot_CommutativeDiagram_Property(va_old_s, dm, dm', out_new_idword,
      pid, ret);  // line 101 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  }
  else
  {
    Lemma_usbtd_slot_allocate_1slot_globals_relationship_False_Properties(s, s');
    Lemma_WKAPI_ChangeTempGVarsAndCounters_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 107 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 108 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- USBTD_slot_deallocate_1slot

function method{:opaque} va_code_USBTD_slot_deallocate_1slot():va_code
{
  va_Block(va_CCons(va_code_USBTD_slot_deallocate_1slot_Impl(), va_CNil()))
}

lemma va_lemma_USBTD_slot_deallocate_1slot(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_USBTD_slot_deallocate_1slot(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 10 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + FFI_USBTD_IsRefTargetUSBTD_StackParamsWords * ARCH_WORD_BYTES
    + 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_retval_space := 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_retval_space))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  var td_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var dm :=
    WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_USBTD_Deallocate1Slot_CommutativeDiagram_Property(va_s0, dm, dm', td_slot, ret)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_USBTD_slot_deallocate_1slot();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_USBTD_slot_deallocate_1slot_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  ghost var td_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
  ghost var ret:uint32 := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  assert InstSaneState(s');  // line 180 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 2 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 182 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_OnUSBTDDeallocation(s, s',
    td_slot, ret);
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_OnUSBTDDeallocation(s,
    s', td_slot, ret);
  assert OpsSaneStateSubset(s');  // line 189 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  if (ret == TRUE)
  {
    ghost var dm := WSM_MapSecureState(s);
    Lemma_USBTD_Deallocate1Slot_ProveCommutativeDiagram_ProvePreCondition(s, td_slot);
    Lemma_USBTD_Deallocate1Slot_ProveCommutativeDiagram(s, dm, td_slot, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_USBTD_Deallocate1Slot_CommutativeDiagram_Property(va_old_s, dm, dm', td_slot, ret); 
      // line 198 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 203 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 204 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- USBTD_slot_submit_and_verify_qtd32

function method{:opaque} va_code_USBTD_slot_submit_and_verify_qtd32():va_code
{
  va_Block(va_CCons(va_code_USBTD_slot_submit_and_verify_qtd32_Impl(), va_CNil()))
}

lemma va_lemma_USBTD_slot_submit_and_verify_qtd32(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_USBTD_slot_submit_and_verify_qtd32(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 53 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES
    + 8 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := 8 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); (wimpdrv_valid_slot_id(wimpdrv_slot) ==>
    wimpdrv_do_get_flag(va_get_globals(va_s0), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete)
    && (wimpdrv_valid_slot_id(wimpdrv_slot) ==> (var wimpdrv_idword :=
    wimpdrv_get_id_word(va_get_globals(va_s0), wimpdrv_slot); wimpdrv_idword !=
    WimpDrv_ID_RESERVED_EMPTY && (var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(va_s0.subjects,
    va_s0.objects, va_s0.id_mappings, wimpdrv_idword); wimpdrv_id in va_s0.subjects.wimp_drvs)))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 4 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 4 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 5 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 5 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 7 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 7 * ARCH_WORD_BYTES)
  ensures  var wimpdrv_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1
    * ARCH_WORD_BYTES); var input_param1:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 5 * ARCH_WORD_BYTES); var input_param2:uint32 := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES); var input_param3:uint32 :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 7 * ARCH_WORD_BYTES); var
    eehci_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 3 *
    ARCH_WORD_BYTES); var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var dm :=
    WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_USBTD_Slot_SubmitAndVerify_CommutativeDiagram_Property(va_s0, dm, va_sM, dm',
    wimpdrv_slot_id, td_slot, ret) &&
    WK_USBTD_Slot_SubmitAndVerify_SubjAndObjsInSamePartition(va_s0, dm, va_sM, dm',
    wimpdrv_slot_id, td_slot, ret)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_USBTD_slot_submit_and_verify_qtd32();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_USBTD_slot_submit_and_verify_qtd32_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  ghost var wimpdrv_slot_id:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
    1 * ARCH_WORD_BYTES);
  ghost var input_param1:uint32 := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
    5 * ARCH_WORD_BYTES);
  ghost var input_param2:uint32 := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
    6 * ARCH_WORD_BYTES);
  ghost var input_param3:uint32 := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
    7 * ARCH_WORD_BYTES);
  ghost var eehci_id:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 3 *
    ARCH_WORD_BYTES);
  ghost var td_slot:uint32 := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
  ghost var ret:uint32 := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  assert InstSaneState(s');  // line 315 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 7 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 317 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 7 * ARCH_WORD_BYTES, 2 * ARCH_WORD_BYTES);
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 7 * ARCH_WORD_BYTES, 3 * ARCH_WORD_BYTES);
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 7 * ARCH_WORD_BYTES, 4 * ARCH_WORD_BYTES);
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 7 * ARCH_WORD_BYTES, 5 * ARCH_WORD_BYTES);
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 7 * ARCH_WORD_BYTES, 6 * ARCH_WORD_BYTES);
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 7 * ARCH_WORD_BYTES, 7 * ARCH_WORD_BYTES);
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_OnUSBTDModification(s, s',
    td_slot, wimpdrv_slot_id, WimpUSBPDev_SlotID_EMPTY, input_param1, input_param2, input_param3,
    USBTDs_TYPE_QTD32, eehci_id, ret);
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_OnUSBTDModification(s,
    s', td_slot, wimpdrv_slot_id, WimpUSBPDev_SlotID_EMPTY, input_param1, input_param2,
    input_param3, USBTDs_TYPE_QTD32, eehci_id, ret);
  assert OpsSaneStateSubset(s');  // line 332 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  if (ret == TRUE)
  {
    ghost var dm := WSM_MapSecureState(s);
    Lemma_USBTD_Slot_SubmitAndVerify_ProveCommutativeDiagram(s, dm, wimpdrv_slot_id, td_slot,
      USBTDs_TYPE_QTD32, WimpUSBPDev_SlotID_EMPTY, input_param1, input_param2, input_param3,
      eehci_id, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_USBTD_Slot_SubmitAndVerify_CommutativeDiagram_Property(va_old_s, dm, va_s2, dm',
      wimpdrv_slot_id, td_slot, ret);  // line 341 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 346 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 347 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- USBTD_slot_submit_and_verify_qh32

function method{:opaque} va_code_USBTD_slot_submit_and_verify_qh32():va_code
{
  va_Block(va_CCons(va_code_USBTD_slot_submit_and_verify_qh32_Impl(), va_CNil()))
}

lemma va_lemma_USBTD_slot_submit_and_verify_qh32(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_USBTD_slot_submit_and_verify_qh32(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 52 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + FFI_USBTD_Qh32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES
    + 9 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := 9 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); (wimpdrv_valid_slot_id(wimpdrv_slot) ==>
    wimpdrv_do_get_flag(va_get_globals(va_s0), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete)
    && (wimpdrv_valid_slot_id(wimpdrv_slot) ==> (var wimpdrv_idword :=
    wimpdrv_get_id_word(va_get_globals(va_s0), wimpdrv_slot); wimpdrv_idword !=
    WimpDrv_ID_RESERVED_EMPTY && (var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(va_s0.subjects,
    va_s0.objects, va_s0.id_mappings, wimpdrv_idword); wimpdrv_id in va_s0.subjects.wimp_drvs)))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 4 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 4 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 5 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 5 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 7 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 7 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 8 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 8 * ARCH_WORD_BYTES)
  ensures  var wimpdrv_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1
    * ARCH_WORD_BYTES); var usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 8 * ARCH_WORD_BYTES); var input_param1:uint32 := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 5 * ARCH_WORD_BYTES); var input_param2:uint32 :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES); var
    input_param3:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 7 *
    ARCH_WORD_BYTES); var eehci_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)
    + 3 * ARCH_WORD_BYTES); var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var dm :=
    WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_USBTD_Slot_SubmitAndVerify_CommutativeDiagram_Property(va_s0, dm, va_sM, dm',
    wimpdrv_slot_id, td_slot, ret) &&
    WK_USBTD_Slot_SubmitAndVerify_SubjAndObjsInSamePartition(va_s0, dm, va_sM, dm',
    wimpdrv_slot_id, td_slot, ret)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_USBTD_slot_submit_and_verify_qh32();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_USBTD_slot_submit_and_verify_qh32_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  ghost var wimpdrv_slot_id:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
    1 * ARCH_WORD_BYTES);
  ghost var usbpdev_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 8
    * ARCH_WORD_BYTES);
  ghost var input_param1:uint32 := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
    5 * ARCH_WORD_BYTES);
  ghost var input_param2:uint32 := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
    6 * ARCH_WORD_BYTES);
  ghost var input_param3:uint32 := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
    7 * ARCH_WORD_BYTES);
  ghost var eehci_id:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 3 *
    ARCH_WORD_BYTES);
  ghost var td_slot:uint32 := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
  ghost var ret:uint32 := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  assert InstSaneState(s');  // line 463 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 8 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 465 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 8 * ARCH_WORD_BYTES, 2 * ARCH_WORD_BYTES);
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 8 * ARCH_WORD_BYTES, 3 * ARCH_WORD_BYTES);
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 8 * ARCH_WORD_BYTES, 4 * ARCH_WORD_BYTES);
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 8 * ARCH_WORD_BYTES, 5 * ARCH_WORD_BYTES);
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 8 * ARCH_WORD_BYTES, 6 * ARCH_WORD_BYTES);
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 8 * ARCH_WORD_BYTES, 7 * ARCH_WORD_BYTES);
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 8 * ARCH_WORD_BYTES, 8 * ARCH_WORD_BYTES);
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_OnUSBTDModification(s, s',
    td_slot, wimpdrv_slot_id, usbpdev_slot, input_param1, input_param2, input_param3,
    USBTDs_TYPE_QH32, eehci_id, ret);
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_OnUSBTDModification(s,
    s', td_slot, wimpdrv_slot_id, usbpdev_slot, input_param1, input_param2, input_param3,
    USBTDs_TYPE_QH32, eehci_id, ret);
  assert OpsSaneStateSubset(s');  // line 481 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  if (ret == TRUE)
  {
    ghost var dm := WSM_MapSecureState(s);
    Lemma_USBTD_Slot_SubmitAndVerify_ProveCommutativeDiagram(s, dm, wimpdrv_slot_id, td_slot,
      USBTDs_TYPE_QH32, usbpdev_slot, input_param1, input_param2, input_param3, eehci_id, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_USBTD_Slot_SubmitAndVerify_CommutativeDiagram_Property(va_old_s, dm, va_s2, dm',
      wimpdrv_slot_id, td_slot, ret);  // line 490 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 495 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 496 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
lemma Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_OnUSBTDAllocation(
    s1:state, s2:state,
    new_td_slot:word, new_idword:word, new_td_type:word, new_pid:word, ret:word
)
    requires OpsSaneStateSubset(s1)
    requires InstSaneState(s2)

    requires ret == TRUE ==> usbtd_map_valid_slot_id(new_td_slot)
    requires (new_td_type == USBTDs_TYPE_QTD32) || (new_td_type == USBTDs_TYPE_QH32) || 
        (new_td_type == USBTDs_TYPE_iTD32) || (new_td_type == USBTDs_TYPE_siTD32)
        // Requirements needed by the following requirements
    requires var globals := wkm_get_globals(s1.wk_mstate);
             var globals' := wkm_get_globals(s2.wk_mstate);
             usbtd_slot_allocate_1slot_globals_relationship(globals, globals', new_td_slot, new_idword, new_td_type, new_pid, ret)

    ensures WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification(wkm_get_globals(s2.wk_mstate))
{
    reveal WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification();

    var globals := wkm_get_globals(s1.wk_mstate);
    var globals' := wkm_get_globals(s2.wk_mstate);

    if(ret == TRUE)
    {
        forall i | usbtd_map_valid_slot_id(i) &&
                TestBit(usbtd_map_get_flags(globals', i), USBTD_SLOT_FLAG_SlotSecure_Bit)
            ensures (usbtd_map_get_type(globals', i) == USBTDs_TYPE_QTD32 || usbtd_map_get_type(globals', i) == USBTDs_TYPE_QH32)
        {
            reveal p_usbtd_equal();
            if(i != new_td_slot)
            {
                assert usbtd_map_get_flags(globals', i) == usbtd_map_get_flags(globals, i);
                assert usbtd_map_get_type(globals', i) == usbtd_map_get_type(globals, i);
            }
            else
            {
                assert usbtd_map_get_flags(globals', i) == 0;
                Lemma_TestBit_ReturnFalseIfANumberIs0();
                assert TestBit(usbtd_map_get_flags(globals', i), USBTD_SLOT_FLAG_SlotSecure_Bit) == false;
            }
        }
    }
}

lemma Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_OnUSBTDAllocation(
    s1:state, s2:state,
    new_td_slot:word, new_idword:word, new_td_type:word, new_pid:word, ret:word
)
    requires OpsSaneStateSubset(s1)
    requires InstSaneState(s2)

    requires ret == TRUE ==> usbtd_map_valid_slot_id(new_td_slot)
    requires (new_td_type == USBTDs_TYPE_QTD32) || (new_td_type == USBTDs_TYPE_QH32) || 
        (new_td_type == USBTDs_TYPE_iTD32) || (new_td_type == USBTDs_TYPE_siTD32)
        // Requirements needed by the following requirements
    requires var globals := wkm_get_globals(s1.wk_mstate);
             var globals' := wkm_get_globals(s2.wk_mstate);
             usbtd_slot_allocate_1slot_globals_relationship(globals, globals', new_td_slot, new_idword, new_td_type, new_pid, ret)

    ensures WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure(wkm_get_globals(s2.wk_mstate))
{
    reveal WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure();

    var globals1 := wkm_get_globals(s1.wk_mstate);
    var globals2 := wkm_get_globals(s2.wk_mstate);

    if(ret == TRUE)
    {
        forall td_slot | usbtd_map_valid_slot_id(td_slot) &&
                usbtd_map_get_pid(globals2, td_slot) != WS_PartitionID(PID_INVALID)
            ensures (var td_type := usbtd_map_get_type(globals2, td_slot);
                assert usbtd_slot_valid_type(globals2, td_slot);
                usbtd_has_clear_content(globals2, td_slot, td_type) || 
                (usbtd_map_get_flags(globals2, td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)))
        {
            reveal p_usbtd_equal();
            reveal p_usbtd_content_equal();
            if(td_slot != new_td_slot)
            {
                var td_type := usbtd_map_get_type(globals2, td_slot);
                assert usbtd_slot_valid_type(globals2, td_slot);
                assert usbtd_slot_valid_type(globals2, td_slot) == usbtd_slot_valid_type(globals1, td_slot);
                
                assert p_usbtd_content_equal(globals1, globals2, td_slot);
                reveal ffi_usbtd_clear_content_stack_and_globals_qtd32();
                reveal ffi_usbtd_clear_content_stack_and_globals_qh32();
                assert usbtd_has_clear_content(globals2, td_slot, td_type) == usbtd_has_clear_content(globals1, td_slot, td_type);
                assert usbtd_map_get_flags(globals2, td_slot) == usbtd_map_get_flags(globals1, td_slot);

                assert usbtd_has_clear_content(globals2, td_slot, td_type) || 
                    (usbtd_map_get_flags(globals2, td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit));
            }
        }
    }
    else
    {
        Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s1, s2);
    }
}

lemma Lemma_USBTD_Allocate1Slot_ProveCommutativeDiagram_ProvePreCondition(s:state, usbtd_idword:word)
    requires OpsSaneState(s)
    requires usbtd_idword != USBTD_ID_INVALID

    ensures usbtd_idword in s.id_mappings.usbtd_to_td
    ensures usbtd_idword in s.id_mappings.usbtd_to_fd
    ensures usbtd_idword in s.id_mappings.usbtd_to_do
{
    assert WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings);
    reveal WK_ValidIDMappings();
}

lemma Lemma_usbtd_slot_allocate_1slot_globals_relationship_False_Properties(s:state, s':state)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s.wk_mstate))
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s'.wk_mstate))

    requires state_equal_except_mstate(s, s')
    requires var globals := wkm_get_globals(s.wk_mstate);
             var globals' := wkm_get_globals(s'.wk_mstate);
             globals_other_gvar_unchanged(globals, globals', G_USBTD_ID_Counter())

    ensures state_equal_except_tempgvar_regs_stack_counters(s, s')
{
    reveal global_non_scratchpad_vars_except_counters_are_unchanged();
}
lemma Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_OnUSBTDDeallocation(
    s1:state, s2:state,
    td_slot:word, ret:word
)
    requires OpsSaneStateSubset(s1)
    requires InstSaneState(s2)

    requires ret == TRUE ==> usbtd_map_valid_slot_id(td_slot)
        // Requirements needed by the following requirements
    requires var globals := wkm_get_globals(s1.wk_mstate);
             var globals' := wkm_get_globals(s2.wk_mstate);
             usbtd_slot_deallocate_1slot_globals_relationship(globals, globals', td_slot, ret)

    ensures WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification(wkm_get_globals(s2.wk_mstate))
{
    reveal WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification();

    var globals := wkm_get_globals(s1.wk_mstate);
    var globals' := wkm_get_globals(s2.wk_mstate);

    if(ret == TRUE)
    {
        forall i | usbtd_map_valid_slot_id(i) &&
                TestBit(usbtd_map_get_flags(globals', i), USBTD_SLOT_FLAG_SlotSecure_Bit)
            ensures (usbtd_map_get_type(globals', i) == USBTDs_TYPE_QTD32 || usbtd_map_get_type(globals', i) == USBTDs_TYPE_QH32)
        {
            reveal p_usbtd_equal();
            if(i != td_slot)
            {
                assert usbtd_map_get_flags(globals', i) == usbtd_map_get_flags(globals, i);
                assert usbtd_map_get_type(globals', i) == usbtd_map_get_type(globals, i);
            }
            else
            {
                assert usbtd_map_get_flags(globals', i) == 0;
                Lemma_TestBit_ReturnFalseIfANumberIs0();
                assert TestBit(usbtd_map_get_flags(globals', i), USBTD_SLOT_FLAG_SlotSecure_Bit) == false;
            }
        }
    }
    else
    {
        assert global_non_scratchpad_vars_are_unchanged(globals, globals');
        reveal global_non_scratchpad_vars_are_unchanged();
        Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s1, s2);
    }
}

lemma Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_OnUSBTDDeallocation(
    s1:state, s2:state,
    in_td_slot:word, ret:word
)
    requires OpsSaneStateSubset(s1)
    requires InstSaneState(s2)

    requires ret == TRUE ==> usbtd_map_valid_slot_id(in_td_slot)
        // Requirements needed by the following requirements
    requires var globals := wkm_get_globals(s1.wk_mstate);
             var globals' := wkm_get_globals(s2.wk_mstate);
             usbtd_slot_deallocate_1slot_globals_relationship(globals, globals', in_td_slot, ret)

    ensures WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure(wkm_get_globals(s2.wk_mstate))
{
    reveal WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure();

    var globals1 := wkm_get_globals(s1.wk_mstate);
    var globals2 := wkm_get_globals(s2.wk_mstate);

    if(ret == TRUE)
    {
        forall td_slot | usbtd_map_valid_slot_id(td_slot) &&
                usbtd_map_get_pid(globals2, td_slot) != WS_PartitionID(PID_INVALID)
            ensures (var td_type := usbtd_map_get_type(globals2, td_slot);
                assert usbtd_slot_valid_type(globals2, td_slot);
                usbtd_has_clear_content(globals2, td_slot, td_type) || 
                (usbtd_map_get_flags(globals2, td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)))
        {
            reveal p_usbtd_equal();
            reveal p_usbtd_content_equal();
            if(td_slot != in_td_slot)
            {
                var td_type := usbtd_map_get_type(globals2, td_slot);
                assert usbtd_slot_valid_type(globals2, td_slot);
                assert usbtd_slot_valid_type(globals2, td_slot) == usbtd_slot_valid_type(globals1, td_slot);
                
                assert p_usbtd_content_equal(globals1, globals2, td_slot);
                reveal ffi_usbtd_clear_content_stack_and_globals_qtd32();
                reveal ffi_usbtd_clear_content_stack_and_globals_qh32();
                assert usbtd_has_clear_content(globals2, td_slot, td_type) == usbtd_has_clear_content(globals1, td_slot, td_type);
                assert usbtd_map_get_flags(globals2, td_slot) == usbtd_map_get_flags(globals1, td_slot);

                assert usbtd_has_clear_content(globals2, td_slot, td_type) || 
                    (usbtd_map_get_flags(globals2, td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit));
            }
        }
    }
    else
    {
        assert global_non_scratchpad_vars_are_unchanged(globals1, globals2);
        reveal global_non_scratchpad_vars_are_unchanged();
        Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s1, s2);
    }
}

lemma Lemma_USBTD_Deallocate1Slot_ProveCommutativeDiagram_ProvePreCondition(s:state, td_slot:word)
    requires OpsSaneState(s)

    requires usbtd_map_valid_slot_id(td_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             pids_is_existing_wimp_pid(globals, usbtd_map_get_pid(globals, td_slot).v)

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, td_slot);
            usbtd_idword != USBTD_ID_INVALID &&
            usbtd_idword in s.id_mappings.usbtd_to_td &&
            usbtd_idword in s.id_mappings.usbtd_to_fd &&
            usbtd_idword in s.id_mappings.usbtd_to_do
{
    var globals := wkm_get_globals(s.wk_mstate);
    assert usbtd_map_get_pid(globals, td_slot) != WS_PartitionID(PID_INVALID);

    // Prove usbtd_idword != USBTD_ID_INVALID
    assert WK_USBTD_Map_ValidGlobalVarValues_IDWords(globals);

    assert WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings);
    reveal WK_ValidIDMappings();
}
lemma Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_OnUSBTDModification(
    s1:state, s2:state,
    td_slot:uint32, wimpdrv_slot_id:word, usbpdev_slot:word, input_param1:uint32, input_param2:uint32, input_param3:uint32, td_type:word, eehci_id:word,
    ret:word
)
    requires OpsSaneStateSubset(s1)
    requires InstSaneState(s2)

    requires ret == TRUE ==> usbtd_map_valid_slot_id(td_slot)
    requires var globals := wkm_get_globals(s1.wk_mstate);
             var globals' := wkm_get_globals(s2.wk_mstate);
             ret == TRUE ==> (
                p_usbtd_slot_submit_and_verify_usbtd_ret_global(globals, globals', td_slot) &&
                p_usbtd_slot_submit_modification_to_usbtd(globals', td_slot, wimpdrv_slot_id, usbpdev_slot, input_param1, input_param2, input_param3, td_type, eehci_id)
             )
    requires var globals := wkm_get_globals(s1.wk_mstate);
             var globals' := wkm_get_globals(s2.wk_mstate);
             ret != TRUE ==> global_non_scratchpad_vars_are_unchanged(globals, globals')

    requires (td_type == USBTDs_TYPE_QTD32) || (td_type == USBTDs_TYPE_QH32)

    ensures WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification(wkm_get_globals(s2.wk_mstate))
{
    reveal WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification();

    var globals := wkm_get_globals(s1.wk_mstate);
    var globals' := wkm_get_globals(s2.wk_mstate);

    if(ret == TRUE)
    {
        forall i | usbtd_map_valid_slot_id(i) &&
                TestBit(usbtd_map_get_flags(globals', i), USBTD_SLOT_FLAG_SlotSecure_Bit)
            ensures (usbtd_map_get_type(globals', i) == USBTDs_TYPE_QTD32 || usbtd_map_get_type(globals', i) == USBTDs_TYPE_QH32)
        {
            reveal p_usbtd_equal();
            if(i != td_slot)
            {
                assert usbtd_map_get_flags(globals', i) == usbtd_map_get_flags(globals, i);
                assert usbtd_map_get_type(globals', i) == usbtd_map_get_type(globals, i);
            }
            else
            {
                assert (usbtd_map_get_type(globals', i) == USBTDs_TYPE_QTD32 || usbtd_map_get_type(globals', i) == USBTDs_TYPE_QH32);
            }
        }
    }
    else
    {
        reveal global_non_scratchpad_vars_are_unchanged();
        Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s1, s2);
    }
}

lemma Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_OnUSBTDModification(
    s1:state, s2:state,
    in_td_slot:uint32, wimpdrv_slot_id:word, usbpdev_slot:word, input_param1:uint32, input_param2:uint32, input_param3:uint32, td_type:word, eehci_id:word,
    ret:word
)
    requires OpsSaneStateSubset(s1)
    requires InstSaneState(s2)

    requires ret == TRUE ==> usbtd_map_valid_slot_id(in_td_slot)
    requires var globals := wkm_get_globals(s1.wk_mstate);
             var globals' := wkm_get_globals(s2.wk_mstate);
             ret == TRUE ==> (
                p_usbtd_slot_submit_and_verify_usbtd_ret_global(globals, globals', in_td_slot) &&
                p_usbtd_slot_submit_modification_to_usbtd(globals', in_td_slot, wimpdrv_slot_id, usbpdev_slot, input_param1, input_param2, input_param3, td_type, eehci_id)
             )
    requires var globals := wkm_get_globals(s1.wk_mstate);
             var globals' := wkm_get_globals(s2.wk_mstate);
             ret != TRUE ==> global_non_scratchpad_vars_are_unchanged(globals, globals')

    requires (td_type == USBTDs_TYPE_QTD32) || (td_type == USBTDs_TYPE_QH32)

    ensures WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure(wkm_get_globals(s2.wk_mstate))
{
    reveal WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure();

    var globals1 := wkm_get_globals(s1.wk_mstate);
    var globals2 := wkm_get_globals(s2.wk_mstate);

    if(ret == TRUE)
    {
        forall td_slot | usbtd_map_valid_slot_id(td_slot) &&
                usbtd_map_get_pid(globals2, td_slot) != WS_PartitionID(PID_INVALID)
            ensures (var td_type := usbtd_map_get_type(globals2, td_slot);
                assert usbtd_slot_valid_type(globals2, td_slot);
                usbtd_has_clear_content(globals2, td_slot, td_type) || 
                (usbtd_map_get_flags(globals2, td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)))
        {
            reveal p_usbtd_equal();
            reveal p_usbtd_content_equal();
            if(td_slot != in_td_slot)
            {
                var td_type := usbtd_map_get_type(globals2, td_slot);
                assert usbtd_slot_valid_type(globals2, td_slot);
                assert usbtd_slot_valid_type(globals2, td_slot) == usbtd_slot_valid_type(globals1, td_slot);
                
                assert p_usbtd_content_equal(globals1, globals2, td_slot);
                reveal ffi_usbtd_clear_content_stack_and_globals_qtd32();
                reveal ffi_usbtd_clear_content_stack_and_globals_qh32();
                assert usbtd_has_clear_content(globals2, td_slot, td_type) == usbtd_has_clear_content(globals1, td_slot, td_type);
                assert usbtd_map_get_flags(globals2, td_slot) == usbtd_map_get_flags(globals1, td_slot);

                assert usbtd_has_clear_content(globals2, td_slot, td_type) || 
                    (usbtd_map_get_flags(globals2, td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit));
            }
        }
    }
    else
    {
        reveal global_non_scratchpad_vars_are_unchanged();
        Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s1, s2);
    }
}
