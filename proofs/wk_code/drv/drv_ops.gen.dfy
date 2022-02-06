include "drv_ops_impl.gen.dfy"
include "drv_ops_impl_wimpdrv_activate.gen.dfy"
include "..\\transition_constraints.s.dfy"
include "..\\proof\\wkapi_commutative_diagram.i.dfy"
//-- WimpDrv_Activate

function method{:opaque} va_code_WimpDrv_Activate():va_code
{
  va_Block(va_CCons(va_code_WimpDrv_Activate_Impl(), va_CNil()))
}

lemma va_lemma_WimpDrv_Activate(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Activate(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 11 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 4 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space) && (var stack_params_space := 4 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var drv_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); drv_id !=
    WimpDrv_ID_RESERVED_EMPTY && WimpDrv_IDWord_ToDrvID(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, drv_id) in va_s0.subjects.wimp_drvs
  requires var new_wimpdrv_idword:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    var new_do_pbase:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); var new_do_pend:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(va_s0.subjects,
    va_s0.objects, va_s0.id_mappings, new_wimpdrv_idword); WK_ValidPMemRegion(new_do_pbase,
    new_do_pend) && wimpdrv_registration_info_must_exist(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, va_s0.objs_addrs, new_wimpdrv_idword, new_do_pbase, new_do_pend)
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
  ensures  var new_wimpdrv_idword:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    var new_wimpdrv_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    drv_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    var dm := WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_DrvActivateToGreenPartition_CommutativeDiagram_Property(va_s0, dm, dm', new_wimpdrv_idword,
    new_wimpdrv_pid, ret)
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
  reveal_va_code_WimpDrv_Activate();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_WimpDrv_Activate_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 88 column 5 of file .\drv/drv_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 4 * ARCH_WORD_BYTES - ARCH_WORD_BYTES,
    ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 90 column 5 of file .\drv/drv_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 97 column 5 of file .\drv/drv_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var new_wimpdrv_idword:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP,
      va_old_s));
    ghost var new_wimpdrv_pid:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s)
      + 1 * ARCH_WORD_BYTES);
    ghost var new_do_pbase:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
      2 * ARCH_WORD_BYTES);
    ghost var new_do_pend:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 3
      * ARCH_WORD_BYTES);
    ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
    ghost var drv_slot:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s) +
      ARCH_WORD_BYTES);
    ghost var dm := WSM_MapSecureState(s);
    Lemma_WimpDrv_Activate_ProveCommutativeDiagram(s, dm, drv_slot, new_wimpdrv_idword,
      new_wimpdrv_pid, new_do_pbase, new_do_pend, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_DrvActivateToGreenPartition_CommutativeDiagram_Property(va_old_s, dm, dm',
      new_wimpdrv_idword, new_wimpdrv_pid, ret);  // line 114 column 9 of file .\drv/drv_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 119 column 9 of file .\drv/drv_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 120 column 9 of file .\drv/drv_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- WimpDrv_Deactivate

function method{:opaque} va_code_WimpDrv_Deactivate():va_code
{
  va_Block(va_CCons(va_code_WimpDrv_Deactivate_Impl(), va_CNil()))
}

lemma va_lemma_WimpDrv_Deactivate(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Deactivate(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ +
    FFI_PMem_ReleaseFromWimps_StackParamsWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var drv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    wimpdrv_valid_slot_id(drv_slot) && pids_is_existing_wimp_pid(va_get_globals(va_s0),
    wimpdrv_get_pid(va_get_globals(va_s0), drv_slot).v) ==> (var wimpdrv_idword :=
    wimpdrv_get_id_word(va_get_globals(va_s0), drv_slot); var wimpdrv_id:Drv_ID :=
    WimpDrv_IDWord_ToDrvID(va_s0.subjects, va_s0.objects, va_s0.id_mappings, wimpdrv_idword);
    wimpdrv_id in va_s0.subjects.wimp_drvs)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES)
  ensures  var drv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var dm :=
    WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_WimpDrv_Deactivate_CommutativeDiagram_Property(va_s0, dm, dm', drv_slot, ret)
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
  reveal_va_code_WimpDrv_Deactivate();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_WimpDrv_Deactivate_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 194 column 5 of file .\drv/drv_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 1 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 196 column 5 of file .\drv/drv_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 203 column 5 of file .\drv/drv_ops.vad
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var drv_slot:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
    ghost var ret:uint32 := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
    ghost var dm := WSM_MapSecureState(s);
    Lemma_WimpDrv_Deactivate_ProveCommutativeDiagram(s, dm, drv_slot, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_WimpDrv_Deactivate_CommutativeDiagram_Property(va_old_s, dm, dm', drv_slot, ret);  // line 215 column 9 of file .\drv/drv_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 220 column 9 of file .\drv/drv_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 221 column 9 of file .\drv/drv_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
