include "eehci_ops_impl.gen.dfy"
include "..\\..\\transition_constraints.s.dfy"
include "..\\..\\proof\\wkapi_commutative_diagram.i.dfy"
//-- EEHCI_Activate

function method{:opaque} va_code_EEHCI_Activate():va_code
{
  va_Block(va_CCons(va_code_EEHCI_Activate_Impl(), va_CNil()))
}

lemma va_lemma_EEHCI_Activate(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_EEHCI_Activate(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ +
    FFI_EEHCI_Activate_ReturnWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space) && (var stack_params_space := 4 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
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
  ensures  var new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var eehci_idword:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES); var
    eehci_handle:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); var eehci_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); var dm := WSM_MapSecureState(va_s0); var dm' :=
    WSM_MapSecureState(va_sM); WK_EEHCI_Activate_CommutativeDiagram_Property(va_s0, dm, dm',
    new_pid, eehci_idword, ret)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  var stack_retval_space := 4 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_globals(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_EEHCI_Activate();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_EEHCI_Activate_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 72 column 5 of file .\dev/usb2/eehci_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 4 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 74 column 5 of file .\dev/usb2/eehci_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 81 column 5 of file .\dev/usb2/eehci_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var new_pid:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
    ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
    ghost var eehci_idword:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s) + 1 *
      ARCH_WORD_BYTES);
    ghost var eehci_handle:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s) + 2 *
      ARCH_WORD_BYTES);
    ghost var eehci_slot:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s) + 3 *
      ARCH_WORD_BYTES);
    ghost var dm := WSM_MapSecureState(s);
    Lemma_EEHCI_Activate_ProveCommutativeDiagram(s, dm, eehci_slot, new_pid, eehci_idword,
      eehci_handle, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_EEHCI_Activate_CommutativeDiagram_Property(va_old_s, dm, dm', new_pid, eehci_idword,
      ret);  // line 96 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 101 column 9 of file .\dev/usb2/eehci_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 102 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- EEHCI_Deactivate

function method{:opaque} va_code_EEHCI_Deactivate():va_code
{
  va_Block(va_CCons(va_code_EEHCI_Deactivate_Impl(), va_CNil()))
}

lemma va_lemma_EEHCI_Deactivate(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_EEHCI_Deactivate(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ +
    FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space) && (var stack_params_space := 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    eehci_valid_slot_id(eehci_slot) && pids_is_existing_wimp_pid(va_get_globals(va_s0),
    eehci_info_get_pid(va_get_globals(va_s0), eehci_slot).v) ==> (var eehci_idword :=
    eehci_mem_get_eehci_id(va_get_globals(va_s0), eehci_slot); var eehci_id:Dev_ID :=
    Map_EEHCIIDWord_ToDevID(va_s0.subjects, va_s0.objects, va_s0.id_mappings, eehci_idword);
    eehci_id in va_s0.subjects.eehcis)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  var eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var dm :=
    WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_EEHCI_Deactivate_CommutativeDiagram_Property(va_s0, dm, dm', eehci_slot, ret)
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
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_globals(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_EEHCI_Deactivate();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_EEHCI_Deactivate_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 175 column 5 of file .\dev/usb2/eehci_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 1 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 177 column 5 of file .\dev/usb2/eehci_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 184 column 5 of file .\dev/usb2/eehci_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var eehci_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
    ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
    ghost var dm := WSM_MapSecureState(s);
    Lemma_EEHCI_Deactivate_ProveCommutativeDiagram(s, dm, eehci_slot, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_EEHCI_Deactivate_CommutativeDiagram_Property(va_old_s, dm, dm', eehci_slot, ret);  // line 196 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 201 column 9 of file .\dev/usb2/eehci_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 202 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- WimpDrv_Read_eEHCI_Config

function method{:opaque} va_code_WimpDrv_Read_eEHCI_Config():va_code
{
  va_Block(va_CCons(va_code_WimpDrv_Read_eEHCI_Config_Impl(), va_CNil()))
}

lemma va_lemma_WimpDrv_Read_eEHCI_Config(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Read_eEHCI_Config(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); ((wimpdrv_valid_slot_id(wimpdrv_slot) ==>
    wimpdrv_do_get_flag(va_get_globals(va_s0), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete)
    && (wimpdrv_valid_slot_id(wimpdrv_slot) ==> (var wimpdrv_idword :=
    wimpdrv_get_id_word(va_get_globals(va_s0), wimpdrv_slot); wimpdrv_idword !=
    WimpDrv_ID_RESERVED_EMPTY && (var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(va_s0.subjects,
    va_s0.objects, va_s0.id_mappings, wimpdrv_idword); wimpdrv_id in va_s0.subjects.wimp_drvs))))
    && (eehci_valid_slot_id(eehci_slot) ==> (var eehci_idword :=
    eehci_mem_get_eehci_id(va_get_globals(va_s0), eehci_slot); eehci_idword != eEHCI_ID_INVALID &&
    (var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, eehci_idword); eehci_id in va_s0.subjects.eehcis)))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2
    * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    var dm := WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    isUInt32(G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset) &&
    WK_WimpDrv_ReadEEHCIFDsDOs_CommutativeDiagram_Property(va_s0, dm, dm', wimpdrv_slot,
    eehci_slot, G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset, ret)
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
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_WimpDrv_Read_eEHCI_Config();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_WimpDrv_Read_eEHCI_Config_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 287 column 5 of file .\dev/usb2/eehci_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 2 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 289 column 5 of file .\dev/usb2/eehci_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 296 column 5 of file .\dev/usb2/eehci_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var wimpdrv_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
    ghost var eehci_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 1
      * ARCH_WORD_BYTES);
    ghost var new_v:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 2 *
      ARCH_WORD_BYTES);
    ghost var dm := WSM_MapSecureState(s);
    Lemma_eehci_slot_offset_AlwaysValidGEEHCIMemAddr(eehci_slot,
      G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset);
    Lemma_WimpDrvReadEEHCIFDDO_ProveCommutativeDiagram(s, dm, wimpdrv_slot, eehci_slot,
      G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_WimpDrv_ReadEEHCIFDsDOs_CommutativeDiagram_Property(va_old_s, dm, dm', wimpdrv_slot,
      eehci_slot, G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset, ret);  // line 310 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 316 column 9 of file .\dev/usb2/eehci_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 317 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- WimpDrv_Write_eEHCI_Config

function method{:opaque} va_code_WimpDrv_Write_eEHCI_Config():va_code
{
  va_Block(va_CCons(va_code_WimpDrv_Write_eEHCI_Config_Impl(), va_CNil()))
}

lemma va_lemma_WimpDrv_Write_eEHCI_Config(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Write_eEHCI_Config(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); ((wimpdrv_valid_slot_id(wimpdrv_slot) ==>
    wimpdrv_do_get_flag(va_get_globals(va_s0), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete)
    && (wimpdrv_valid_slot_id(wimpdrv_slot) ==> (var wimpdrv_idword :=
    wimpdrv_get_id_word(va_get_globals(va_s0), wimpdrv_slot); wimpdrv_idword !=
    WimpDrv_ID_RESERVED_EMPTY && (var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(va_s0.subjects,
    va_s0.objects, va_s0.id_mappings, wimpdrv_idword); wimpdrv_id in va_s0.subjects.wimp_drvs))))
    && (eehci_valid_slot_id(eehci_slot) ==> (var eehci_idword :=
    eehci_mem_get_eehci_id(va_get_globals(va_s0), eehci_slot); eehci_idword != eEHCI_ID_INVALID &&
    (var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, eehci_idword); eehci_id in va_s0.subjects.eehcis)))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2
    * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    var dm := WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    isUInt32(G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset) &&
    WK_WimpDrv_WriteEEHCIFDsDOs_CommutativeDiagram_Property(va_s0, dm, dm', wimpdrv_slot,
    eehci_slot, G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset, new_v, ret)
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
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_globals(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_WimpDrv_Write_eEHCI_Config();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_WimpDrv_Write_eEHCI_Config_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 406 column 5 of file .\dev/usb2/eehci_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 2 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 408 column 5 of file .\dev/usb2/eehci_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 415 column 5 of file .\dev/usb2/eehci_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var wimpdrv_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
    ghost var eehci_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 1
      * ARCH_WORD_BYTES);
    ghost var new_v:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 2 *
      ARCH_WORD_BYTES);
    ghost var dm := WSM_MapSecureState(s);
    Lemma_eehci_slot_offset_AlwaysValidGEEHCIMemAddr(eehci_slot,
      G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset);
    Lemma_WimpDrvWriteEEHCIFDDO_ProveCommutativeDiagram(s, dm, wimpdrv_slot, eehci_slot,
      G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset, new_v, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_WimpDrv_WriteEEHCIFDsDOs_CommutativeDiagram_Property(va_old_s, dm, dm', wimpdrv_slot,
      eehci_slot, G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset, new_v, ret);  // line 429 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 435 column 9 of file .\dev/usb2/eehci_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 436 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- WimpDrv_Read_eEHCI_Status

function method{:opaque} va_code_WimpDrv_Read_eEHCI_Status():va_code
{
  va_Block(va_CCons(va_code_WimpDrv_Read_eEHCI_Status_Impl(), va_CNil()))
}

lemma va_lemma_WimpDrv_Read_eEHCI_Status(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Read_eEHCI_Status(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); ((wimpdrv_valid_slot_id(wimpdrv_slot) ==>
    wimpdrv_do_get_flag(va_get_globals(va_s0), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete)
    && (wimpdrv_valid_slot_id(wimpdrv_slot) ==> (var wimpdrv_idword :=
    wimpdrv_get_id_word(va_get_globals(va_s0), wimpdrv_slot); wimpdrv_idword !=
    WimpDrv_ID_RESERVED_EMPTY && (var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(va_s0.subjects,
    va_s0.objects, va_s0.id_mappings, wimpdrv_idword); wimpdrv_id in va_s0.subjects.wimp_drvs))))
    && (eehci_valid_slot_id(eehci_slot) ==> (var eehci_idword :=
    eehci_mem_get_eehci_id(va_get_globals(va_s0), eehci_slot); eehci_idword != eEHCI_ID_INVALID &&
    (var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, eehci_idword); eehci_id in va_s0.subjects.eehcis)))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2
    * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    var dm := WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    isUInt32(G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset) &&
    WK_WimpDrv_ReadEEHCIFDsDOs_CommutativeDiagram_Property(va_s0, dm, dm', wimpdrv_slot,
    eehci_slot, G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset, ret)
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
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_WimpDrv_Read_eEHCI_Status();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_WimpDrv_Read_eEHCI_Status_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 521 column 5 of file .\dev/usb2/eehci_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 2 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 523 column 5 of file .\dev/usb2/eehci_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 530 column 5 of file .\dev/usb2/eehci_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var wimpdrv_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
    ghost var eehci_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 1
      * ARCH_WORD_BYTES);
    ghost var new_v:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 2 *
      ARCH_WORD_BYTES);
    ghost var dm := WSM_MapSecureState(s);
    Lemma_eehci_slot_offset_AlwaysValidGEEHCIMemAddr(eehci_slot,
      G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset);
    Lemma_WimpDrvReadEEHCIFDDO_ProveCommutativeDiagram(s, dm, wimpdrv_slot, eehci_slot,
      G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_WimpDrv_ReadEEHCIFDsDOs_CommutativeDiagram_Property(va_old_s, dm, dm', wimpdrv_slot,
      eehci_slot, G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset, ret);  // line 544 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 550 column 9 of file .\dev/usb2/eehci_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 551 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- WimpDrv_Write_eEHCI_Status

function method{:opaque} va_code_WimpDrv_Write_eEHCI_Status():va_code
{
  va_Block(va_CCons(va_code_WimpDrv_Write_eEHCI_Status_Impl(), va_CNil()))
}

lemma va_lemma_WimpDrv_Write_eEHCI_Status(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Write_eEHCI_Status(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); ((wimpdrv_valid_slot_id(wimpdrv_slot) ==>
    wimpdrv_do_get_flag(va_get_globals(va_s0), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete)
    && (wimpdrv_valid_slot_id(wimpdrv_slot) ==> (var wimpdrv_idword :=
    wimpdrv_get_id_word(va_get_globals(va_s0), wimpdrv_slot); wimpdrv_idword !=
    WimpDrv_ID_RESERVED_EMPTY && (var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(va_s0.subjects,
    va_s0.objects, va_s0.id_mappings, wimpdrv_idword); wimpdrv_id in va_s0.subjects.wimp_drvs))))
    && (eehci_valid_slot_id(eehci_slot) ==> (var eehci_idword :=
    eehci_mem_get_eehci_id(va_get_globals(va_s0), eehci_slot); eehci_idword != eEHCI_ID_INVALID &&
    (var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, eehci_idword); eehci_id in va_s0.subjects.eehcis)))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2
    * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    var dm := WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    isUInt32(G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset) &&
    WK_WimpDrv_WriteEEHCIFDsDOs_CommutativeDiagram_Property(va_s0, dm, dm', wimpdrv_slot,
    eehci_slot, G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset, new_v, ret)
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
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_globals(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_WimpDrv_Write_eEHCI_Status();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_WimpDrv_Write_eEHCI_Status_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 640 column 5 of file .\dev/usb2/eehci_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 2 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 642 column 5 of file .\dev/usb2/eehci_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 649 column 5 of file .\dev/usb2/eehci_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var wimpdrv_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
    ghost var eehci_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 1
      * ARCH_WORD_BYTES);
    ghost var new_v:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 2 *
      ARCH_WORD_BYTES);
    ghost var dm := WSM_MapSecureState(s);
    Lemma_eehci_slot_offset_AlwaysValidGEEHCIMemAddr(eehci_slot,
      G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset);
    Lemma_WimpDrvWriteEEHCIFDDO_ProveCommutativeDiagram(s, dm, wimpdrv_slot, eehci_slot,
      G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset, new_v, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_WimpDrv_WriteEEHCIFDsDOs_CommutativeDiagram_Property(va_old_s, dm, dm', wimpdrv_slot,
      eehci_slot, G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset, new_v, ret);  // line 663 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 669 column 9 of file .\dev/usb2/eehci_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 670 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- WimpDrv_Read_eEHCI_USBTDReg

function method{:opaque} va_code_WimpDrv_Read_eEHCI_USBTDReg():va_code
{
  va_Block(va_CCons(va_code_WimpDrv_Read_eEHCI_USBTDReg_Impl(), va_CNil()))
}

lemma va_lemma_WimpDrv_Read_eEHCI_USBTDReg(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Read_eEHCI_USBTDReg(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); ((wimpdrv_valid_slot_id(wimpdrv_slot) ==>
    wimpdrv_do_get_flag(va_get_globals(va_s0), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete)
    && (wimpdrv_valid_slot_id(wimpdrv_slot) ==> (var wimpdrv_idword :=
    wimpdrv_get_id_word(va_get_globals(va_s0), wimpdrv_slot); wimpdrv_idword !=
    WimpDrv_ID_RESERVED_EMPTY && (var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(va_s0.subjects,
    va_s0.objects, va_s0.id_mappings, wimpdrv_idword); wimpdrv_id in va_s0.subjects.wimp_drvs))))
    && (eehci_valid_slot_id(eehci_slot) ==> (var eehci_idword :=
    eehci_mem_get_eehci_id(va_get_globals(va_s0), eehci_slot); eehci_idword != eEHCI_ID_INVALID &&
    (var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, eehci_idword); eehci_id in va_s0.subjects.eehcis)))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES)
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var usbtd_reg_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP,
    va_s0)); var dm := WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_WimpDrv_ReadEEHCIUSBTDReg_CommutativeDiagram_Property(va_s0, dm, dm', wimpdrv_slot,
    eehci_slot, usbtd_reg_slot, ret)
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
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_WimpDrv_Read_eEHCI_USBTDReg();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_WimpDrv_Read_eEHCI_USBTDReg_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 757 column 5 of file .\dev/usb2/eehci_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 3 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 759 column 5 of file .\dev/usb2/eehci_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 766 column 5 of file .\dev/usb2/eehci_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var wimpdrv_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
    ghost var eehci_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 1
      * ARCH_WORD_BYTES);
    ghost var usbtd_reg_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s)
      + 2 * ARCH_WORD_BYTES);
    ghost var dm := WSM_MapSecureState(s);
    Lemma_WimpDrvWriteEEHCIUSBTDReg_ProveCommutativeDiagram_ProvePreConditions(eehci_slot,
      usbtd_reg_slot);
    Lemma_WimpDrvReadEEHCIUSBTDReg_ProveCommutativeDiagram(s, dm, wimpdrv_slot, eehci_slot,
      usbtd_reg_slot, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_WimpDrv_ReadEEHCIUSBTDReg_CommutativeDiagram_Property(va_old_s, dm, dm',
      wimpdrv_slot, eehci_slot, usbtd_reg_slot, ret);  // line 780 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 786 column 9 of file .\dev/usb2/eehci_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 787 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- WimpDrv_Write_eEHCI_USBTDReg

function method{:opaque} va_code_WimpDrv_Write_eEHCI_USBTDReg():va_code
{
  va_Block(va_CCons(va_code_WimpDrv_Write_eEHCI_USBTDReg_Impl(), va_CNil()))
}

lemma va_lemma_WimpDrv_Write_eEHCI_USBTDReg(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Write_eEHCI_USBTDReg(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 20 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 4 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); ((wimpdrv_valid_slot_id(wimpdrv_slot) ==>
    wimpdrv_do_get_flag(va_get_globals(va_s0), wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete)
    && (wimpdrv_valid_slot_id(wimpdrv_slot) ==> (var wimpdrv_idword :=
    wimpdrv_get_id_word(va_get_globals(va_s0), wimpdrv_slot); wimpdrv_idword !=
    WimpDrv_ID_RESERVED_EMPTY && (var wimpdrv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(va_s0.subjects,
    va_s0.objects, va_s0.id_mappings, wimpdrv_idword); wimpdrv_id in va_s0.subjects.wimp_drvs))))
    && (eehci_valid_slot_id(eehci_slot) ==> (var eehci_idword :=
    eehci_mem_get_eehci_id(va_get_globals(va_s0), eehci_slot); eehci_idword != eEHCI_ID_INVALID &&
    (var eehci_id:Dev_ID := Map_EEHCIIDWord_ToDevID(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, eehci_idword); eehci_id in va_s0.subjects.eehcis)))
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
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var usbtd_reg_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var new_v:word := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM),
    va_get_reg(ESP, va_s0)); var dm := WSM_MapSecureState(va_s0); var dm' :=
    WSM_MapSecureState(va_sM); WK_WimpDrv_WriteEEHCIUSBTDReg_CommutativeDiagram_Property(va_s0, dm,
    va_sM, dm', wimpdrv_slot, eehci_slot, usbtd_reg_id, new_v, ret)
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
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_globals(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_WimpDrv_Write_eEHCI_USBTDReg();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_WimpDrv_Write_eEHCI_USBTDReg_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 878 column 5 of file .\dev/usb2/eehci_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 3 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 880 column 5 of file .\dev/usb2/eehci_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 887 column 5 of file .\dev/usb2/eehci_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var wimpdrv_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
    ghost var eehci_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 1
      * ARCH_WORD_BYTES);
    ghost var usbtd_reg_id:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
      2 * ARCH_WORD_BYTES);
    ghost var new_v:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 3 *
      ARCH_WORD_BYTES);
    ghost var dm := WSM_MapSecureState(s);
    Lemma_WimpDrvWriteEEHCIUSBTDReg_ProveCommutativeDiagram_ProvePreConditions(eehci_slot,
      usbtd_reg_id);
    Lemma_WimpDrvWriteEEHCIUSBTDReg_ProveCommutativeDiagram(s, dm, wimpdrv_slot, eehci_slot,
      usbtd_reg_id, new_v, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_WimpDrv_WriteEEHCIUSBTDReg_CommutativeDiagram_Property(va_old_s, dm, va_s2, dm',
      wimpdrv_slot, eehci_slot, usbtd_reg_id, new_v, ret);  // line 902 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 908 column 9 of file .\dev/usb2/eehci_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 909 column 9 of file .\dev/usb2/eehci_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
