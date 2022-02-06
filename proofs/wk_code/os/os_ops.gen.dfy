include "os_ops_impl.gen.dfy"
include "..\\transition_constraints.s.dfy"
include "..\\proof\\wkapi_commutative_diagram.i.dfy"
//-- OS_Activate_MainMem_ByPAddr

function method{:opaque} va_code_OS_Activate_MainMem_ByPAddr():va_code
{
  va_Block(va_CCons(va_code_OS_Activate_MainMem_ByPAddr_Impl(), va_CNil()))
}

lemma va_lemma_OS_Activate_MainMem_ByPAddr(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_OS_Activate_MainMem_ByPAddr(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := FFI_PMem_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires ins_valid_pmem_activate_main_mem_in_os(va_s0, va_get_reg(ESP, va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES)
  ensures  var paddr_end:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var paddr_start:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var dm :=
    WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    OS_Activate_MainMem_ByPAddr_CommutativeDiagram_Property(va_s0, dm, dm', paddr_start, paddr_end,
    ret)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := FFI_PMem_ActivateInOS_ReturnWords * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_os_mem_active_map(va_sM, va_update_objects(va_sM, va_update_subjects(va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))))
{
  reveal_va_code_OS_Activate_MainMem_ByPAddr();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_OS_Activate_MainMem_ByPAddr_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 66 column 5 of file .\os/os_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 2 * ARCH_WORD_BYTES - ARCH_WORD_BYTES,
    ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 68 column 5 of file .\os/os_ops.vad
  reveal_ffi_pmem_activate_main_mem_in_os_stack_and_statevars();
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_OS_Activate_MainMem_ByPAddr_WhenReturnTRUE_ProveWK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 76 column 5 of file .\os/os_ops.vad
  ghost var paddr_end:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
    ARCH_WORD_BYTES);
  ghost var paddr_start:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var dm := WSM_MapSecureState(s);
    Lemma_OS_Activate_MainMem_ByPAddr_ProveCommutativeDiagram(s, dm, paddr_start, paddr_end, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert OS_Activate_MainMem_ByPAddr_CommutativeDiagram_Property(s, dm, dm', paddr_start,
      paddr_end, ret);  // line 88 column 9 of file .\os/os_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 93 column 9 of file .\os/os_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 94 column 9 of file .\os/os_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- OS_Deactivate_MainMem_ByPAddr

function method{:opaque} va_code_OS_Deactivate_MainMem_ByPAddr():va_code
{
  va_Block(va_CCons(va_code_OS_Deactivate_MainMem_ByPAddr_Impl(), va_CNil()))
}

lemma va_lemma_OS_Deactivate_MainMem_ByPAddr(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_OS_Deactivate_MainMem_ByPAddr(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := FFI_PMem_DeactivateFromOS_StackParamsWords * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires ins_valid_pmem_deactivate_main_mem_from_os(va_s0, va_get_reg(ESP, va_s0))
  requires var paddr_end:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var paddr_start:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var dm := WSM_MapSecureState(va_s0);
    P_OS_Deactivate_MainMem_ByPAddr_AdditonalPreConditions(va_s0, dm, paddr_start, paddr_end)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES)
  ensures  var paddr_end:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var paddr_start:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var dm := WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    OS_Deactivate_MainMem_ByPAddr_CommutativeDiagram_Property(va_s0, dm, dm', paddr_start,
    paddr_end)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_os_mem_active_map(va_sM, va_update_objects(va_sM, va_update_subjects(va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))))
{
  reveal_va_code_OS_Deactivate_MainMem_ByPAddr();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_OS_Deactivate_MainMem_ByPAddr_Impl(va_b1, va_s0, va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert InstSaneState(s');  // line 161 column 5 of file .\os/os_ops.vad
  Lemma_IsAddrInStack_Property(va_get_reg(ESP, va_old_s), 2 * ARCH_WORD_BYTES, ARCH_WORD_BYTES);
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + ARCH_WORD_BYTES);  // line 163 column 5 of file .\os/os_ops.vad
  Lemma_OS_Deactivate_MainMem_ByPAddr_ProveStackAddr(va_get_reg(ESP, va_old_s));
  assert IsAddrInStack(va_get_reg(ESP, va_old_s) + 2 * ARCH_WORD_BYTES - ARCH_WORD_BYTES);  // line 165 column 5 of file .\os/os_ops.vad
  reveal_ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars();
  reveal_global_non_scratchpad_vars_are_unchanged();
  Lemma_OS_Deactivate_MainMem_ByPAddr_ProveWK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(s,
    s');
  Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s, s');
  Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s,
    s');
  assert OpsSaneStateSubset(s');  // line 173 column 5 of file .\os/os_ops.vad
  ghost var paddr_end:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) +
    ARCH_WORD_BYTES);
  ghost var paddr_start:word := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
  ghost var dm := WSM_MapSecureState(s);
  Lemma_OS_Deactivate_MainMem_ByPAddr_ProveCommutativeDiagram(s, dm, paddr_start, paddr_end, s');
  ghost var dm' := WSM_MapSecureState(va_s2);
  assert OS_Deactivate_MainMem_ByPAddr_CommutativeDiagram_Property(s, dm, dm', paddr_start,
    paddr_end);  // line 182 column 5 of file .\os/os_ops.vad
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- OS_Activate_AllReleasedPEHCIsAndUSBPDevs

function method{:opaque} va_code_OS_Activate_AllReleasedPEHCIsAndUSBPDevs():va_code
{
  va_Block(va_CCons(va_code_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_Impl(), va_CNil()))
}

lemma va_lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_OS_Activate_AllReleasedPEHCIsAndUSBPDevs(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 3 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 15 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := 1 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space))
  requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(va_s0.subjects, usbpdev_id) ==>
    va_s0.subjects.usbpdevs[usbpdev_id].active_in_os == false
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  OpsSaneState(va_sM)
  ensures  WSM_IsSecureOps(va_s0, va_sM)
  ensures  is_valid_addr(va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES)
  ensures  is_valid_vaddr(va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES)
  ensures  var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var dm :=
    WSM_MapSecureState(va_s0); var dm' := WSM_MapSecureState(va_sM);
    WK_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_CommutativeDiagram_Property(va_s0, dm, dm', ret)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space) && va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_subjects(va_sM, va_update_objects(va_sM, va_update_mem(va_sM, va_update_ok(va_sM,
    va_s0)))))))))))))
{
  reveal_va_code_OS_Activate_AllReleasedPEHCIsAndUSBPDevs();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_Impl(va_b1, va_s0,
    va_sM);
  ghost var s := va_old_s;
  ghost var s' := va_s2;
  assert OpsSaneStateSubset(s');  // line 251 column 5 of file .\os/os_ops.vad
  reveal_global_non_scratchpad_vars_are_unchanged();
  ghost var ret:word := stack_get_val(va_get_mem(va_s2), va_get_reg(ESP, va_old_s));
  if (ret == TRUE)
  {
    ghost var dm := WSM_MapSecureState(s);
    Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveCommutativeDiagram(s, dm,
      PID_RESERVED_OS_PARTITION, s');
    ghost var dm' := WSM_MapSecureState(va_s2);
    assert WK_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_CommutativeDiagram_Property(s, dm, dm',
      ret);  // line 262 column 9 of file .\os/os_ops.vad
  }
  else
  {
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s, s');
    assert OpsSaneState(s);  // line 267 column 9 of file .\os/os_ops.vad
    assert WSM_IsSecureOps(s, s');  // line 268 column 9 of file .\os/os_ops.vad
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
lemma Lemma_OS_Activate_MainMem_ByPAddr_WhenReturnTRUE_ProveWK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(
    s:state, s':state
)
    requires OpsSaneStateSubset(s)
    requires InstSaneState(s')

    requires var s_wkm := s.wk_mstate; 
             var old_esp := x86_get_reg(s_wkm, ESP);
             var stack_params_space := FFI_PMem_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES)
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pmem_activate_main_mem_in_os(s, old_esp)
    requires var mem := wkm_stack_get_all(s'.wk_mstate);
             ffi_preserve_old_stack(s.wk_mstate, mem, FFI_PMem_ActivateInOS_ReturnWords)
        // Requirements needed by the following requirements
    requires var mem := wkm_stack_get_all(s'.wk_mstate);
             ffi_pmem_activate_main_mem_in_os_stack_and_statevars(s, mem, s'.subjects, s'.objects, s'.os_mem_active_map);
    
    ensures WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate))
{
    reveal ffi_preserve_old_stack();
    reveal ffi_pmem_activate_main_mem_in_os_stack_and_statevars();
    reveal WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions();
}

lemma Lemma_OS_Deactivate_MainMem_ByPAddr_ProveWK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(
    s:state, s':state
)
    requires OpsSaneStateSubset(s)
    requires InstSaneState(s')

    requires var s_wkm := s.wk_mstate; 
             var old_esp := x86_get_reg(s_wkm, ESP);
             var stack_params_space := FFI_PMem_DeactivateFromOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES)
                // Because the caller needs to allocate stack, even <esp + stack_retval_space> is a stack address
    requires var s_wkm := s.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pmem_deactivate_main_mem_from_os(s, old_esp)
    requires var mem := wkm_stack_get_all(s'.wk_mstate);
             ffi_preserve_old_stack(s.wk_mstate, mem, FFI_PMem_DeactivateFromOS_ReturnWords)
        // Requirements needed by the following requirements
    requires var mem := wkm_stack_get_all(s'.wk_mstate);
             ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars(s, mem, s'.subjects, s'.objects, s'.os_mem_active_map);
    
    ensures WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate))
{
    reveal ffi_preserve_old_stack();
    reveal ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars();
    reveal WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions();
}

lemma Lemma_OS_Deactivate_MainMem_ByPAddr_ProveStackAddr(base:word)
    requires isUInt32(base + ARCH_WORD_BYTES)
    requires IsAddrInStack(base + ARCH_WORD_BYTES)
    ensures IsAddrInStack(base + 2 * ARCH_WORD_BYTES - ARCH_WORD_BYTES)
{
    // Dafny can automatically prove this lemma
}
