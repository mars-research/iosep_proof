include "../dev/usb2/usb_pdev_utils.gen.dfy"
include "../dev/usb2/eehci_info.gen.dfy"
include "..\\state_properties.s.dfy"
include "..\\proof\\state_map_OpsSaneState.i.dfy"
include "..\\state_properties_OpsSaneStateSubset.i.dfy"
//-- OS_Activate_MainMem_ByPAddr_Impl

function method{:opaque} va_code_OS_Activate_MainMem_ByPAddr_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_CALL_PMem_ActivateInOS(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_op_word_reg(EAX)),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_OS_Activate_MainMem_ByPAddr_Impl(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_OS_Activate_MainMem_ByPAddr_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := FFI_PMem_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires ins_valid_pmem_activate_main_mem_in_os(va_s0, va_get_reg(ESP, va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_PMem_ActivateInOS_ReturnWords)
  ensures  ffi_pmem_activate_main_mem_in_os_stack_and_statevars(va_s0, va_get_mem(va_sM),
    va_sM.subjects, va_sM.objects, va_sM.os_mem_active_map)
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
  reveal_va_code_OS_Activate_MainMem_ByPAddr_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_ffi_preserve_old_stack();
  reveal_ffi_pmem_activate_main_mem_in_os_stack_and_statevars();
  ghost var va_b4, va_s4 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b5, va_s5 := va_lemma_MOV_ToReg(va_b4, va_s4, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_Reg1ToReg6(va_b5, va_s5, va_sM);
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_PUSH(va_b11, va_s11, va_sM, va_op_word_reg(ECX));
  ghost var va_b13, va_s13 := va_lemma_PUSH(va_b12, va_s12, va_sM, va_op_word_reg(EBX));
  ghost var va_b14, va_s14 := va_lemma_CALL_PMem_ActivateInOS(va_b13, va_s13, va_sM);
  ghost var va_b15, va_s15 := va_lemma_Load(va_b14, va_s14, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0);
  ghost var va_b16, va_s16 := va_lemma_Store(va_b15, va_s15, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(EAX));
  ghost var va_b17, va_s17 := va_lemma_POP_VOID(va_b16, va_s16, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_b18, va_s18 := va_lemma_POP_Reg1ToReg6(va_b17, va_s17, va_sM);
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s19, va_sM);
}
//--
//-- OS_Deactivate_MainMem_ByPAddr_Impl

function method{:opaque} va_code_OS_Deactivate_MainMem_ByPAddr_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_CALL_PMem_DeactivateFromOS(),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))
}

lemma va_lemma_OS_Deactivate_MainMem_ByPAddr_Impl(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_OS_Deactivate_MainMem_ByPAddr_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := FFI_PMem_DeactivateFromOS_StackParamsWords * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires ins_valid_pmem_deactivate_main_mem_from_os(va_s0, va_get_reg(ESP, va_s0))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  ffi_preserve_old_stack(va_s0.wk_mstate, va_get_mem(va_sM),
    FFI_PMem_DeactivateFromOS_ReturnWords)
  ensures  ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars(va_s0, va_get_mem(va_sM),
    va_sM.subjects, va_sM.objects, va_sM.os_mem_active_map)
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
  reveal_va_code_OS_Deactivate_MainMem_ByPAddr_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_ffi_preserve_old_stack();
  reveal_ffi_pmem_deactivate_main_mem_from_os_stack_and_statevars();
  ghost var va_b4, va_s4 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b5, va_s5 := va_lemma_MOV_ToReg(va_b4, va_s4, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_Reg1ToReg6(va_b5, va_s5, va_sM);
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_PUSH(va_b11, va_s11, va_sM, va_op_word_reg(ECX));
  ghost var va_b13, va_s13 := va_lemma_PUSH(va_b12, va_s12, va_sM, va_op_word_reg(EBX));
  ghost var va_b14, va_s14 := va_lemma_CALL_PMem_DeactivateFromOS(va_b13, va_s13, va_sM);
  ghost var va_b15, va_s15 := va_lemma_POP_VOID(va_b14, va_s14, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_b16, va_s16 := va_lemma_POP_Reg1ToReg6(va_b15, va_s15, va_sM);
  ghost var va_b17, va_s17 := va_lemma_POP_OneReg(va_b16, va_s16, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s17, va_sM);
}
//--
//-- OS_Activate_AllReleasedPEHCIsAndUSBPDevs_Impl

function method{:opaque} va_code_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(ECX)),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_const_word(PID_INVALID)),
    va_CCons(va_code_eehci_find_slot_not_in_partition(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_const_word(PID_INVALID)),
    va_CCons(va_code_usbpdev_find_slot_not_in_partition(),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_usbpdevlist_clear_all_devices(),
    va_CCons(va_code_AXIOM_Assign_USBPDevs_To_OS_Partition(), va_CCons(va_code_PUSH_Reg1ToReg6(),
    va_CCons(va_code_CALL_PEHCI_ActivateInOS(), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))), va_CNil()))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 20}
  va_lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_Impl(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires OpsSaneState(va_s0)
  requires var stack_req_space := 3 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 15 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := 1 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(va_get_globals(va_s0)); var
    empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
    (ret == TRUE ==> usb_is_usbpdev_addr_valid(empty_addr)) && (ret == TRUE ==> (forall
    addr:USBPDev_Addr :: addr in all_non_empty_addrs ==> (var dev_id :=
    Map_USBPDevAddr_ToDevID(va_s0.subjects, va_s0.objects, va_s0.id_mappings, addr); dev_id in
    va_s0.subjects.usbpdevs)))
  ensures  forall dev_id:Dev_ID :: dev_id in va_s0.activate_conds.ehci_activate_cond ==> dev_id in
    va_s0.subjects.os_devs
  ensures  var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(va_get_globals(va_s0)); ((((ret ==
    TRUE ==> (forall i:word :: eehci_valid_slot_id(i) ==> eehci_info_get_pid(va_get_globals(va_s0),
    i) == WS_PartitionID(PID_INVALID))) && (ret == TRUE ==> (forall i:word ::
    usbpdev_valid_slot_id(i) ==> usbpdev_get_pid(va_get_globals(va_s0), i) ==
    WS_PartitionID(PID_INVALID)))) && (ret == TRUE ==>
    P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE(va_s0, va_sM, all_non_empty_addrs)))
    && (ret != TRUE ==> global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0),
    va_get_globals(va_sM)))) && (ret != TRUE ==> state_equal_except_mstate(va_s0, va_sM))
  ensures  OpsSaneStateSubset(va_sM)
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
  reveal_va_code_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b6, va_s6 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(ECX));
  ghost var orig_esp := va_get_reg(ESP, va_s6);
  Lemma_WK_ValidState_DevsActivateCond_Property(va_old_s);
  ghost var va_b9, va_s9 := va_lemma_PUSH_VOID(va_b6, va_s6, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b10, va_s10 := va_lemma_PUSH(va_b9, va_s9, va_sM, va_const_word(PID_INVALID));
  ghost var va_b11, va_s11 := va_lemma_eehci_find_slot_not_in_partition(va_b10, va_s10, va_sM);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0);
  ghost var va_b13, va_s13 := va_lemma_POP_VOID(va_b12, va_s12, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_PUSH_VOID(va_b16, va_s15, va_s14, 1 * ARCH_WORD_BYTES);
    ghost var va_b18, va_s18 := va_lemma_PUSH(va_b17, va_s17, va_s14, va_const_word(PID_INVALID));
    ghost var va_b19, va_s19 := va_lemma_usbpdev_find_slot_not_in_partition(va_b18, va_s18, va_s14);
    ghost var va_b20, va_s20 := va_lemma_Load(va_b19, va_s19, va_s14, va_op_word_reg(ECX),
      va_op_word_reg(ESP), 0);
    ghost var va_b21, va_s21 := va_lemma_POP_VOID(va_b20, va_s20, va_s14, 2 * ARCH_WORD_BYTES);
    ghost var va_s22, va_c22, va_b22 := va_lemma_block(va_b21, va_s21, va_s14);
    ghost var va_cond_c22, va_s23:va_state := va_lemma_ifElse(va_get_ifCond(va_c22),
      va_get_ifTrue(va_c22), va_get_ifFalse(va_c22), va_s21, va_s22);
    if (va_cond_c22)
    {
      ghost var va_b24 := va_get_block(va_get_ifTrue(va_c22));
      ghost var this1 := va_s23;
      ghost var va_b26, va_s26 := va_lemma_usbpdevlist_clear_all_devices(va_b24, va_s23, va_s22);
      ghost var this2 := va_s26;
      Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_PropertiesOfusbpdevlist_clear_all_devices(va_old_s,
        this1, this2);
      ghost var all_non_empty_addrs :=
        usbpdevlist_get_all_non_empty_addrs(va_get_globals(va_old_s));
      assert usbpdev_clear_multi_non_mstate_relationship(va_old_s, this2, all_non_empty_addrs);  // line 257 column 13 of file .\os/os_ops_impl.vad
      ghost var va_b31, va_s31 := va_lemma_AXIOM_Assign_USBPDevs_To_OS_Partition(va_b26, va_s26,
        va_s22);
      ghost var this3 := va_s31;
      reveal_usbpdev_clear_multi_non_mstate_relationship();
      reveal_P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE_ForClearUSBPDevs();
      reveal_P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ModificationsToUSBPDevsOnly();
      assert P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE_ForClearUSBPDevs(va_old_s,
        this3, all_non_empty_addrs);  // line 268 column 13 of file .\os/os_ops_impl.vad
      ghost var va_b37, va_s37 := va_lemma_PUSH_Reg1ToReg6(va_b31, va_s31, va_s22);
      ghost var this4 := va_s37;
      assert P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE_ForClearUSBPDevs(va_old_s,
        this4, all_non_empty_addrs);  // line 273 column 13 of file .\os/os_ops_impl.vad
      ghost var va_b40, va_s40 := va_lemma_CALL_PEHCI_ActivateInOS(va_b37, va_s37, va_s22);
      assert IsAddrInStack(va_get_reg(ESP, va_s40) - ARCH_WORD_BYTES);  // line 275 column 13 of file .\os/os_ops_impl.vad
      assert ffi_pehci_activate_in_os_stack_and_statevars(this4, va_s40.subjects, va_s40.objects); 
        // line 276 column 13 of file .\os/os_ops_impl.vad
      assert va_get_reg(ESP, va_s40) == orig_esp - 6 * ARCH_WORD_BYTES;  // line 277 column 13 of file .\os/os_ops_impl.vad
      ghost var va_b44, va_s44 := va_lemma_POP_Reg1ToReg6(va_b40, va_s40, va_s22);
      ghost var va_b45, va_s45 := va_lemma_Store(va_b44, va_s44, va_s22, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      ghost var va_b46, va_s46 := va_lemma_POP_TwoRegs(va_b45, va_s45, va_s22, va_op_reg_reg(EAX),
        va_op_reg_reg(ECX));
      ghost var va_b47, va_s47 := va_lemma_POP_OneReg(va_b46, va_s46, va_s22, va_op_reg_reg(EBP));
      Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveP_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE(va_old_s,
        this4, va_s47, all_non_empty_addrs);
      assert P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE(va_old_s, va_s47,
        all_non_empty_addrs);  // line 287 column 13 of file .\os/os_ops_impl.vad
      Lemma_P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE_ProveWK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(va_old_s,
        va_s47);
      assert WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(va_s47.subjects,
        va_s47.objects, va_s47.id_mappings, va_get_globals(va_s47));  // line 292 column 13 of file .\os/os_ops_impl.vad
      va_s22 := va_lemma_empty(va_s47, va_s22);
    }
    else
    {
      ghost var va_b52 := va_get_block(va_get_ifFalse(va_c22));
      ghost var va_b53, va_s53 := va_lemma_Store(va_b52, va_s23, va_s22, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s53) == va_get_globals(va_old_s);  // line 298 column 13 of file .\os/os_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s53));
      ghost var va_b56, va_s56 := va_lemma_POP_TwoRegs(va_b53, va_s53, va_s22, va_op_reg_reg(EAX),
        va_op_reg_reg(ECX));
      ghost var va_b57, va_s57 := va_lemma_POP_OneReg(va_b56, va_s56, va_s22, va_op_reg_reg(EBP));
      va_s22 := va_lemma_empty(va_s57, va_s22);
    }
    va_s14 := va_lemma_empty(va_s22, va_s14);
  }
  else
  {
    ghost var va_b58 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b59, va_s59 := va_lemma_Store(va_b58, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s59) == va_get_globals(va_old_s);  // line 309 column 9 of file .\os/os_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s59));
    ghost var va_b62, va_s62 := va_lemma_POP_TwoRegs(va_b59, va_s59, va_s14, va_op_reg_reg(EAX),
      va_op_reg_reg(ECX));
    ghost var va_b63, va_s63 := va_lemma_POP_OneReg(va_b62, va_s62, va_s14, va_op_reg_reg(EBP));
    va_s14 := va_lemma_empty(va_s63, va_s14);
  }
  reveal_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions();
  Lemma_OpsSaneStateSubset_HoldIfUSBTDsAreUnchanged(va_old_s, va_s14);
  va_sM := va_lemma_empty(va_s14, va_sM);
}
//--
// Additional Pre-condition of <OS_Deactivate_MainMem_ByPAddr>: No red device defines transfer to os_tds/fds/dos
predicate P_OS_Deactivate_MainMem_ByPAddr_AdditonalPreConditions(
    s:state, dm:DM_State, 
    paddr_start:word, paddr_end:word
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WK_ValidPMemRegion(paddr_start, paddr_end)
        // Properties specific to OS_Activate_MainMem_ByPAddr
{
    var result := os_external_objs_to_be_deactivated(s.subjects, s.objects, s.os_mem_active_map, paddr_start, paddr_end);
    var os_tds := result.1;
    var os_fds := result.2;
    var os_dos := result.3;

    var properties_to_prove := (os_tds <= AllTDIDs(dm.objects)) &&
            (os_fds <= AllFDIDs(dm.objects)) &&
            (os_dos <= AllDOIDs(dm.objects)) &&

            (forall id :: id in os_tds
                    ==> DM_ObjPID(dm.objects, id.oid) == dm.red_pid) &&
            (forall id :: id in os_fds
                    ==> DM_ObjPID(dm.objects, id.oid) == dm.red_pid) &&
            (forall id :: id in os_dos
                    ==> DM_ObjPID(dm.objects, id.oid) == dm.red_pid);

    (properties_to_prove ==> P_RedDevsHaveNoTransferToGivenRedObjsAtAnyTime(dm, os_tds, os_fds, os_dos))
}
// Predicate: Properties of OS_Activate_AllReleasedPEHCIsAndUSBPDevs When returning TRUE
predicate {:opaque} P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE(s1:state, s2:state, addrs:set<USBPDev_Addr>)
    requires WK_ValidSubjs_SubjIDs(s1.subjects)
    requires WK_ValidObjs(s1.subjects, s1.objects)
    requires WK_ValidIDMappings(s1.subjects, s1.objects, s1.id_mappings)

    requires forall dev_id :: dev_id in s1.activate_conds.ehci_activate_cond
                ==> dev_id in s1.subjects.os_devs
        // Requirement from <WK_ValidState_DevsActivateCond>

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
        // Requirement: The USBPDev must be located at a non-empty address
    requires forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(s1.subjects, s1.objects, s1.id_mappings, addr) in s1.subjects.usbpdevs
{
    var t := usbpdev_addrs_to_subjs_fds_dos_ids(s1, addrs);
    var usbpdev_ids:set<Dev_ID> := t.0;
    var usbpdev_fd_ids:set<FD_ID> := t.1;
    var usbpdev_do_ids:set<DO_ID> := t.2;

    // Immutable state variables
    s1.objs_addrs == s2.objs_addrs &&
    s1.id_mappings == s2.id_mappings &&
    s1.activate_conds == s2.activate_conds &&
    s1.ok == s2.ok &&

    // Other subjects are unchanged
    s2.subjects.wimp_drvs == s1.subjects.wimp_drvs &&
    s2.subjects.eehcis == s1.subjects.eehcis &&
    s2.subjects.os_drvs == s1.subjects.os_drvs &&

    // Other objects are unchanged
    s1.objects.eehci_hcoded_tds == s2.objects.eehci_hcoded_tds &&
    s1.objects.eehci_other_tds == s2.objects.eehci_other_tds &&
    s1.objects.eehci_fds == s2.objects.eehci_fds &&
    s1.objects.eehci_dos == s2.objects.eehci_dos &&
    s1.objects.usbtd_tds == s2.objects.usbtd_tds &&
    s1.objects.usbtd_fds == s2.objects.usbtd_fds &&
    s1.objects.usbtd_dos == s2.objects.usbtd_dos &&
    s1.objects.wimpdrv_dos == s2.objects.wimpdrv_dos &&

    P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ModificationsToPEHCIsOnly(s1, s2) &&
    P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ModificationsToUSBPDevsOnly(s1, s2, addrs) &&

    (true)
}

// Predicate: Properties of OS_Activate_AllReleasedPEHCIsAndUSBPDevs's modifications to USBPDevs When returning TRUE
predicate {:opaque} P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE_ForClearUSBPDevs(s1:state, s2:state, addrs:set<USBPDev_Addr>)
    requires WK_ValidSubjs_SubjIDs(s1.subjects)
    requires WK_ValidObjs(s1.subjects, s1.objects)
    requires WK_ValidIDMappings(s1.subjects, s1.objects, s1.id_mappings)

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
        // Requirement: The USBPDev must be located at a non-empty address
    requires forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(s1.subjects, s1.objects, s1.id_mappings, addr) in s1.subjects.usbpdevs
{
    var t := usbpdev_addrs_to_subjs_fds_dos_ids(s1, addrs);
    var usbpdev_ids:set<Dev_ID> := t.0;
    var usbpdev_fd_ids:set<FD_ID> := t.1;
    var usbpdev_do_ids:set<DO_ID> := t.2;

    // Immutable state variables
    s1.objs_addrs == s2.objs_addrs &&
    s1.id_mappings == s2.id_mappings &&
    s1.activate_conds == s2.activate_conds &&
    s1.ok == s2.ok &&

    // Other subjects are unchanged
    s2.subjects.wimp_drvs == s1.subjects.wimp_drvs &&
    s2.subjects.eehcis == s1.subjects.eehcis &&
    s2.subjects.os_drvs == s1.subjects.os_drvs &&
    s2.subjects.os_devs == s1.subjects.os_devs &&

    // Other objects are unchanged
    s1.objects.os_tds == s2.objects.os_tds &&
    s1.objects.os_fds == s2.objects.os_fds &&
    s1.objects.os_dos == s2.objects.os_dos &&
    s1.objects.eehci_hcoded_tds == s2.objects.eehci_hcoded_tds &&
    s1.objects.eehci_other_tds == s2.objects.eehci_other_tds &&
    s1.objects.eehci_fds == s2.objects.eehci_fds &&
    s1.objects.eehci_dos == s2.objects.eehci_dos &&
    s1.objects.usbtd_tds == s2.objects.usbtd_tds &&
    s1.objects.usbtd_fds == s2.objects.usbtd_fds &&
    s1.objects.usbtd_dos == s2.objects.usbtd_dos &&
    s1.objects.wimpdrv_dos == s2.objects.wimpdrv_dos &&

    P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ModificationsToUSBPDevsOnly(s1, s2, addrs) &&

    (true)
}

// Predicate: Properties of OS_Activate_AllReleasedPEHCIsAndUSBPDevs's modifications to PEHCIs' subjects and objects
predicate {:opaque} P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ModificationsToPEHCIsOnly(s1:state, s2:state)
    requires WK_ValidSubjs_SubjIDs(s1.subjects)
    requires WK_ValidObjs(s1.subjects, s1.objects)
    requires forall dev_id :: dev_id in s1.activate_conds.ehci_activate_cond
                ==> dev_id in s1.subjects.os_devs
        // Requirement from <WK_ValidState_DevsActivateCond>
{
    var pehci_ids := WSM_AllDevIDs_pEHCIs(s1.subjects, s1.activate_conds);
    var pehci_hcoded_td_ids := WSM_HCodedTDsOwnedByOSDevs(s1, pehci_ids);
    var pehci_td_ids := WSM_TDsOwnedByOSDevs(s1, pehci_ids);
    var pehci_fd_ids := WSM_FDsOwnedByOSDevs(s1, pehci_ids);
    var pehci_do_ids := WSM_DOsOwnedByOSDevs(s1, pehci_ids);

    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    assert forall id:: id in pehci_hcoded_td_ids ==> id in s1.objects.os_tds;
    assert forall id:: id in pehci_td_ids ==> id in s1.objects.os_tds;
    assert forall id:: id in pehci_fd_ids ==> id in s1.objects.os_fds;
    assert forall id:: id in pehci_do_ids ==> id in s1.objects.os_dos;

    //// Subjects modification due to PEHCIs activation
    (forall id :: id in s1.subjects.os_devs <==> id in s2.subjects.os_devs) &&
    (forall id :: id in s1.subjects.os_devs && id !in pehci_ids
        ==> s2.subjects.os_devs[id] == s1.subjects.os_devs[id]
            // Other OS devices are unchanged
    ) &&
    (forall id :: id in pehci_ids
        ==> (s2.subjects.os_devs[id].hcoded_td_id == s1.subjects.os_devs[id].hcoded_td_id &&
                s2.subjects.os_devs[id].td_ids == s1.subjects.os_devs[id].td_ids &&
                s2.subjects.os_devs[id].fd_ids == s1.subjects.os_devs[id].fd_ids &&
                s2.subjects.os_devs[id].do_ids == s1.subjects.os_devs[id].do_ids &&
                s2.subjects.os_devs[id].pid == WS_PartitionID(PID_RESERVED_OS_PARTITION)
            )
            // All PEHCIs are moved to the OS partition
    ) &&

    // PEHCIs are activated in the OS partition
    (
        var to_clear_objs := pehci_td_ids - pehci_hcoded_td_ids;

        // Clear the objects being activated (i.e., ClearObjs)
        var temp_tds := WSM_ClearOSTDs(s1.objects.os_tds, to_clear_objs);
        var temp_fds := WSM_ClearOSFDs(s1.objects.os_fds, pehci_fd_ids);
        var temp_dos := WSM_ClearOSDOs(s1.objects.os_dos, pehci_do_ids);

        // Modify the PID of these objects (i.e., SetPbjsPIDs)
        var os_tds' := WSM_SetOSTDsPIDs(temp_tds, pehci_td_ids, WS_PartitionID(PID_RESERVED_OS_PARTITION));
        var os_fds' := WSM_SetOSFDsPIDs(temp_fds, pehci_fd_ids, WS_PartitionID(PID_RESERVED_OS_PARTITION));
        var os_dos' := WSM_SetOSDOsPIDs(temp_dos, pehci_do_ids, WS_PartitionID(PID_RESERVED_OS_PARTITION));

        s2.objects.os_tds == os_tds' &&
        s2.objects.os_fds == os_fds' &&
        s2.objects.os_dos == os_dos'
    ) &&

    (true)
}

// Predicate: Properties of OS_Activate_AllReleasedPEHCIsAndUSBPDevs's modifications to USBPDevs' subjects and objects
predicate {:opaque} P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ModificationsToUSBPDevsOnly(s1:state, s2:state, addrs:set<USBPDev_Addr>)
    requires WK_ValidSubjs_SubjIDs(s1.subjects)
    requires WK_ValidObjs(s1.subjects, s1.objects)
    requires WK_ValidIDMappings(s1.subjects, s1.objects, s1.id_mappings)

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
        // Requirement: The USBPDev must be located at a non-empty address
    requires forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(s1.subjects, s1.objects, s1.id_mappings, addr) in s1.subjects.usbpdevs
{
    var t := usbpdev_addrs_to_subjs_fds_dos_ids(s1, addrs);
    var usbpdev_ids:set<Dev_ID> := t.0;
    var usbpdev_fd_ids:set<FD_ID> := t.1;
    var usbpdev_do_ids:set<DO_ID> := t.2;

    // Correct modifications to subjects
    MapGetKeys(s2.subjects.usbpdevs) == MapGetKeys(s1.subjects.usbpdevs) &&
    (forall id :: id in s1.subjects.usbpdevs
                ==> s2.subjects.usbpdevs[id].hcoded_td_id == s1.subjects.usbpdevs[id].hcoded_td_id &&
                    s2.subjects.usbpdevs[id].fd_ids == s1.subjects.usbpdevs[id].fd_ids &&
                    s2.subjects.usbpdevs[id].do_ids == s1.subjects.usbpdevs[id].do_ids) &&
    (forall id :: id in s1.subjects.usbpdevs
                ==> s2.subjects.usbpdevs[id].active_in_os == true) &&

    // Correct modifications to objects
    s1.objects.usbpdev_tds == s2.objects.usbpdev_tds &&

    // In <usbpdev_fds>, clear the contents of the USBPDev's FDs only
    MapGetKeys(s1.objects.usbpdev_fds) == MapGetKeys(s2.objects.usbpdev_fds) &&
    (
        forall id :: id in s1.objects.usbpdev_fds
            ==> (id in usbpdev_fd_ids ==> WSM_IsFDClearVal(s2.objects.usbpdev_fds, id)) &&
                (id !in usbpdev_fd_ids ==> s1.objects.usbpdev_fds[id] == s2.objects.usbpdev_fds[id])
    ) &&

    // In <usbpdev_dos>, clear the contents of the USBPDev's DOs only
    MapGetKeys(s1.objects.usbpdev_dos) == MapGetKeys(s2.objects.usbpdev_dos) &&
    (
        forall id :: id in s1.objects.usbpdev_dos
            ==> (id in usbpdev_do_ids ==> WSM_IsDOClearVal(s2.objects.usbpdev_dos, id)) &&
                (id !in usbpdev_do_ids ==> s1.objects.usbpdev_dos[id] == s2.objects.usbpdev_dos[id])
    ) &&

    (true)
}
lemma Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_PropertiesOfusbpdevlist_clear_all_devices(old_s:state, s1:state, s2:state)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(old_s.wk_mstate))
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(wkm_get_globals(old_s.wk_mstate))
    requires WK_ValidSubjs_SubjIDs(old_s.subjects)
    requires WK_ValidObjs(old_s.subjects, old_s.objects)
    requires WK_ValidIDMappings(old_s.subjects, old_s.objects, old_s.id_mappings)
    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(old_s.wk_mstate));
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in all_non_empty_addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
        // Requirement: The USBPDev must be located at a non-empty address
    requires var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(old_s.wk_mstate));
             forall addr :: addr in all_non_empty_addrs
                ==> Map_USBPDevAddr_ToDevID(old_s.subjects, old_s.objects, old_s.id_mappings, addr) in old_s.subjects.usbpdevs

    requires wkm_get_globals(s1.wk_mstate) == wkm_get_globals(old_s.wk_mstate)
    requires state_equal_except_mstate(s1, old_s)
        // Property between old_s and s1

    requires var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(s1.wk_mstate));
             usbpdev_clear_multi_non_mstate_relationship(s1, s2, all_non_empty_addrs);
        // Property between s1 and s2

    ensures var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(old_s.wk_mstate));
             usbpdev_clear_multi_non_mstate_relationship(old_s, s2, all_non_empty_addrs);
{
    reveal usbpdev_clear_multi_non_mstate_relationship();

    // Prove usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(s1.wk_mstate)) == usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(old_s.wk_mstate));
    assert usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(s1.wk_mstate)) ==
            usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(old_s.wk_mstate));

    // Prove usbpdev_addrs_to_subjs_fds_dos_ids(old_s, all_non_empty_addrs) == usbpdev_addrs_to_subjs_fds_dos_ids(s1, all_non_empty_addrs)
    var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(s1.wk_mstate)); 
    assert usbpdev_addrs_to_subjs_fds_dos_ids(old_s, all_non_empty_addrs) == usbpdev_addrs_to_subjs_fds_dos_ids(s1, all_non_empty_addrs);

    // Prove the post-condition
    var t := usbpdev_addrs_to_subjs_fds_dos_ids(old_s, all_non_empty_addrs);
    var usbpdev_ids:set<Dev_ID> := t.0;
    var usbpdev_fd_ids:set<FD_ID> := t.1;
    var usbpdev_do_ids:set<DO_ID> := t.2;

    forall id | id in old_s.objects.usbpdev_fds
        ensures (id in usbpdev_fd_ids ==> WSM_IsFDClearVal(s2.objects.usbpdev_fds, id)) &&
                (id !in usbpdev_fd_ids ==> old_s.objects.usbpdev_fds[id] == s2.objects.usbpdev_fds[id])
    {
        assert (id in usbpdev_fd_ids ==> WSM_IsFDClearVal(s2.objects.usbpdev_fds, id)) &&
                (id !in usbpdev_fd_ids ==> old_s.objects.usbpdev_fds[id] == s2.objects.usbpdev_fds[id]);
    }

    forall id | id in old_s.objects.usbpdev_dos
        ensures (id in usbpdev_do_ids ==> WSM_IsDOClearVal(s2.objects.usbpdev_dos, id)) &&
                (id !in usbpdev_do_ids ==> old_s.objects.usbpdev_dos[id] == s2.objects.usbpdev_dos[id])
    {
        assert (id in usbpdev_do_ids ==> WSM_IsDOClearVal(s2.objects.usbpdev_dos, id)) &&
                (id !in usbpdev_do_ids ==> old_s.objects.usbpdev_dos[id] == s2.objects.usbpdev_dos[id]);
    }
}

lemma Lemma_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ProveP_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE(
    old_s:state, s1:state, s2:state, addrs:set<USBPDev_Addr>
)
    requires WK_ValidSubjs_SubjIDs(old_s.subjects)
    requires WK_ValidObjs(old_s.subjects, old_s.objects)
    requires WK_ValidIDMappings(old_s.subjects, old_s.objects, old_s.id_mappings)

    requires var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
    requires forall addr :: addr in addrs
                ==> Map_USBPDevAddr_ToDevID(old_s.subjects, old_s.objects, old_s.id_mappings, addr) in old_s.subjects.usbpdevs
        // Requirements for P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE_ForClearUSBPDevs
    requires ValidState(s1)
    requires var old_esp := x86_get_reg(s1.wk_mstate, ESP);
             var stack_params_space := FFI_PEHCI_ActivateInOS_StackParamsWords * ARCH_WORD_BYTES;
             IsAddrInStack(old_esp + stack_params_space - ARCH_WORD_BYTES); 
    requires var s_wkm := s1.wk_mstate;
             var old_esp := x86_get_reg(s_wkm, ESP); 
             ins_valid_pEHCI_ActivateInOS(s1, old_esp)
    requires s1.objs_addrs == s2.objs_addrs &&
            s1.id_mappings == s2.id_mappings &&
            s1.activate_conds == s2.activate_conds &&
            s1.ok == s2.ok
        // Requirements for ffi_pehci_activate_in_os_stack_and_statevars
    requires forall dev_id :: dev_id in old_s.activate_conds.ehci_activate_cond
                ==> dev_id in old_s.subjects.os_devs
        // Requirements for P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE

    requires P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE_ForClearUSBPDevs(old_s, s1, addrs)
    requires ffi_pehci_activate_in_os_stack_and_statevars(s1, s2.subjects, s2.objects)

    ensures P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE(old_s, s2, addrs)
{
    reveal P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ModificationsToPEHCIsOnly();
    reveal P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ModificationsToUSBPDevsOnly();
    reveal P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE_ForClearUSBPDevs();
    reveal ffi_pehci_activate_in_os_stack_and_statevars();
    reveal P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE();


    // Immutable state variables
    assert old_s.objs_addrs == s2.objs_addrs &&
    old_s.id_mappings == s2.id_mappings &&
    old_s.activate_conds == s2.activate_conds &&
    old_s.ok == s2.ok &&

    // Other subjects are unchanged
    s2.subjects.wimp_drvs == old_s.subjects.wimp_drvs &&
    s2.subjects.eehcis == old_s.subjects.eehcis &&
    s2.subjects.os_drvs == old_s.subjects.os_drvs &&

    // Other objects are unchanged
    old_s.objects.eehci_hcoded_tds == s2.objects.eehci_hcoded_tds &&
    old_s.objects.eehci_other_tds == s2.objects.eehci_other_tds &&
    old_s.objects.eehci_fds == s2.objects.eehci_fds &&
    old_s.objects.eehci_dos == s2.objects.eehci_dos &&
    old_s.objects.usbtd_tds == s2.objects.usbtd_tds &&
    old_s.objects.usbtd_fds == s2.objects.usbtd_fds &&
    old_s.objects.usbtd_dos == s2.objects.usbtd_dos &&
    old_s.objects.wimpdrv_dos == s2.objects.wimpdrv_dos &&

    P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ModificationsToPEHCIsOnly(old_s, s2) &&
    P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ModificationsToUSBPDevsOnly(old_s, s2, addrs);
}

lemma Lemma_P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE_ProveWK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(
    s:state, s':state
)
    requires OpsSaneStateSubset(s)
    requires InstSaneState(s')

    requires forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
        // Requirement from <WK_ValidState_DevsActivateCond>

    requires var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(s.wk_mstate));
             var empty_addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
             usb_is_usbpdev_addr_valid(empty_addr) &&
             (forall addr :: addr in all_non_empty_addrs
                ==> addr != usb_parse_usbpdev_addr(empty_addr))
        // Requirement: The USBPDev must be located at a non-empty address
    requires var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(s.wk_mstate));
             forall addr :: addr in all_non_empty_addrs
                ==> Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, addr) in s.subjects.usbpdevs

    requires var all_non_empty_addrs := usbpdevlist_get_all_non_empty_addrs(wkm_get_globals(s.wk_mstate));
             P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE(s, s', all_non_empty_addrs)
        // Requirement: Properties of <usbpdevlist_clear_all_devices>
    
    ensures WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate))
{
    reveal P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_WhenReturnTRUE();
    reveal P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ModificationsToPEHCIsOnly();
    reveal P_OS_Activate_AllReleasedPEHCIsAndUSBPDevs_ModificationsToUSBPDevsOnly();
    reveal WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions();
}
