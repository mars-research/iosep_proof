include "wk_partition_ops_utils.s.dfy"
include "partition_id_ops.gen.dfy"
include "wk_partition_ops_impl.gen.dfy"
include "dev/usb2/eehci_info.gen.dfy"
include "dev/usb2/usb_pdev_utils.gen.dfy"
include "dev/usb2/usb_tds_utils.gen.dfy"
include "drv/drv_ops_utils.gen.dfy"
include "transition_constraints.s.dfy"
include "proof\\wkapi_commutative_diagram.i.dfy"
//-- WK_EmptyPartitionCreate

function method{:opaque} va_code_WK_EmptyPartitionCreate():va_code
{
  va_Block(va_CCons(va_code_WK_EmptyPartitionCreate_Impl(), va_CNil()))
}

lemma{:timeLimitMultiplier 5} va_lemma_WK_EmptyPartitionCreate(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state, pid_slot:word)
  requires va_require(va_b0, va_code_WK_EmptyPartitionCreate(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 13 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES)
  ensures  var new_pid:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    dm_new_pid:Partition_ID := WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(new_pid));
    var dm := WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_EmptyPartitionCreate_CommutativeDiagram_Property(dm, dm', dm_new_pid, ret)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_globals(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI,
    va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_WK_EmptyPartitionCreate();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2, va_ltmp3 := va_lemma_WK_EmptyPartitionCreate_Impl(va_b1, va_s0, va_sM);
  pid_slot := va_ltmp3;
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 73 column 5 of file .\wk_partition_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 2 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 75 column 5 of file .\wk_partition_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 82 column 5 of file .\wk_partition_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var dm := WSM_MapSecureState(s);
    ghost var new_pid:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s) +
      ARCH_WORD_BYTES);
    Lemma_WK_EmptyPartitionCreate_ProveCommutativeDiagram(s, dm, pid_slot, new_pid, s');
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 95 column 9 of file .\wk_partition_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 96 column 9 of file .\wk_partition_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- WK_EmptyPartitionDestroy

function method{:opaque} va_code_WK_EmptyPartitionDestroy():va_code
{
  va_Block(va_CCons(va_code_WK_EmptyPartitionDestroy_Impl(), va_CNil()))
}

lemma{:timeLimitMultiplier 5} va_lemma_WK_EmptyPartitionDestroy(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WK_EmptyPartitionDestroy(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES)
  ensures  var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var ret:word
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var dm_pid:Partition_ID :=
    WSM_MapWSParititonID_ToAbstractPartitionID(WS_PartitionID(pid)); var dm :=
    WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_EmptyPartitionDestroy_CommutativeDiagram_Property(dm, dm', dm_pid, ret)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_globals(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI,
    va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_WK_EmptyPartitionDestroy();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_WK_EmptyPartitionDestroy_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 161 column 5 of file .\wk_partition_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 1 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 163 column 5 of file .\wk_partition_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 170 column 5 of file .\wk_partition_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var dm := WSM_MapSecureState(s);
    ghost var pid:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
    Lemma_WK_EmptyPartitionDestroy_ProveCommutativeDiagram(s, dm, pid, s');
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 183 column 9 of file .\wk_partition_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 184 column 9 of file .\wk_partition_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
