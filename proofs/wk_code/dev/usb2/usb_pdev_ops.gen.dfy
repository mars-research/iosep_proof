include "usb_pdev_ops_impl.gen.dfy"
include "..\\..\\transition_constraints.s.dfy"
include "..\\..\\proof\\wkapi_commutative_diagram.i.dfy"
//-- USBPDev_Activate

function method{:opaque} va_code_USBPDev_Activate():va_code
{
  va_Block(va_CCons(va_code_USBPDev_ActivateIntoWimpPartition_Impl(), va_CNil()))
}

lemma va_lemma_USBPDev_Activate(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_USBPDev_Activate(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 15 *
    ARCH_WORD_BYTES + 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space)
    && (var stack_params_space := 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(va_s0.subjects, usbpdev_id) ==>
    va_s0.subjects.usbpdevs[usbpdev_id].active_in_os == false
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES)
  ensures  var new_pid := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_usbpdev_addr_low := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_usbpdev_addr_high := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP,
    va_s0)); var usbpdev_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var dm := WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_USBPDev_Activate_CommutativeDiagram_Property(va_s0, dm, dm', usbpdev_slot, new_pid,
    new_usbpdev_addr_low, new_usbpdev_addr_high, ret)
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
    va_update_objects(va_sM, va_update_globals(va_sM, va_update_mem(va_sM, va_update_ok(va_sM,
    va_s0)))))))))))))
{
  reveal_va_code_USBPDev_Activate();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_USBPDev_ActivateIntoWimpPartition_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 73 column 5 of file .\dev/usb2/usb_pdev_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 3 * ARCH_WORD_BYTES - ARCH_WORD_BYTES,
    ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 75 column 5 of file .\dev/usb2/usb_pdev_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 82 column 5 of file .\dev/usb2/usb_pdev_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var new_pid := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
    ghost var new_usbpdev_addr_low := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s)
      + 1 * ARCH_WORD_BYTES);
    ghost var new_usbpdev_addr_high := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP,
      va_old_s) + 2 * ARCH_WORD_BYTES);
    ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
    ghost var usbpdev_slot:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s) +
      ARCH_WORD_BYTES);
    ghost var dm := WSM_MapSecureState(s);
    Lemma_USBPDev_Activate_ProveCommutativeDiagram(s, dm, usbpdev_slot, new_pid,
      new_usbpdev_addr_low, new_usbpdev_addr_high, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_USBPDev_Activate_CommutativeDiagram_Property(va_old_s, dm, dm', usbpdev_slot,
      new_pid, new_usbpdev_addr_low, new_usbpdev_addr_high, ret);  // line 98 column 9 of file .\dev/usb2/usb_pdev_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 103 column 9 of file .\dev/usb2/usb_pdev_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 104 column 9 of file .\dev/usb2/usb_pdev_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- USBPDev_Deactivate

function method{:opaque} va_code_USBPDev_Deactivate():va_code
{
  va_Block(va_CCons(va_code_USBPDev_DeactivateFromWimpPartition_Impl(), va_CNil()))
}

lemma va_lemma_USBPDev_Deactivate(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_USBPDev_Deactivate(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 20 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(va_s0.subjects, usbpdev_id) ==>
    va_s0.subjects.usbpdevs[usbpdev_id].active_in_os == false
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  var usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var dm :=
    WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_USBPDev_Deactivate_CommutativeDiagram_Property(va_s0, dm, dm', usbpdev_slot, ret)
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
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_globals(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_USBPDev_Deactivate();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_USBPDev_DeactivateFromWimpPartition_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 169 column 5 of file .\dev/usb2/usb_pdev_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 1 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 171 column 5 of file .\dev/usb2/usb_pdev_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 178 column 5 of file .\dev/usb2/usb_pdev_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var usbpdev_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
    ghost var ret:uint32 := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
    ghost var dm := WSM_MapSecureState(s);
    Lemma_USBPDev_Deactivate_ProveCommutativeDiagram(s, dm, usbpdev_slot, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_USBPDev_Deactivate_CommutativeDiagram_Property(va_old_s, dm, dm', usbpdev_slot, ret);
      // line 190 column 9 of file .\dev/usb2/usb_pdev_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 195 column 9 of file .\dev/usb2/usb_pdev_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 196 column 9 of file .\dev/usb2/usb_pdev_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
