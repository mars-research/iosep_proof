include "eehci.s.dfy"
include "eehci_ops_impl_private.gen.dfy"
include "eehci_info.gen.dfy"
include "eehci_mem_utils.gen.dfy"
include "usb_tds_utils.gen.dfy"
include "../../partition_id_ops.gen.dfy"
include "../../drv/drv_ops_utils.gen.dfy"
//-- _WimpDrv_Write_eEHCI_USBTDReg_check_new_value
//--
//-- _WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty1
//--
//-- _WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty2
//--
//-- EEHCI_Activate_Impl

function method{:opaque} va_code_EEHCI_Activate_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(ECX)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH_VOID(4 * ARCH_WORD_BYTES),
    va_CCons(va_code_CALL_EEHCI_Activate(), va_CCons(va_code_Load(va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 1 *
    ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 2 *
    ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(ESP), 3 *
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(4 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(ECX)), va_CCons(va_code_PUSH(va_const_word(0)),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code__eehci_info_update_slot_to_valid_pid(), va_CCons(va_code_POP_VOID(3 *
    ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_Store(va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES,
    va_op_word_reg(EDX)), va_CCons(va_code_Store(va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES,
    va_op_word_reg(EDI)), va_CNil()))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(eEHCI_ID_INVALID)), va_CCons(va_code_Store(va_op_word_reg(EBP), 3 *
    ARCH_WORD_BYTES, va_const_word(eEHCI_Handle_INVALID)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES,
    va_const_word(eEHCI_SlotID_EMPTY)), va_CNil())))))), va_CNil()))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(eEHCI_ID_INVALID)), va_CCons(va_code_Store(va_op_word_reg(EBP), 3 *
    ARCH_WORD_BYTES, va_const_word(eEHCI_Handle_INVALID)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES,
    va_const_word(eEHCI_SlotID_EMPTY)), va_CNil())))))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))
}

lemma{:timeLimitMultiplier 20} va_lemma_EEHCI_Activate_Impl(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_EEHCI_Activate_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ +
    FFI_EEHCI_Activate_ReturnWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space) && (var stack_params_space := 4 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var eehci_idword:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES); var
    eehci_handle:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); var eehci_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); ((((((ret == TRUE ==> (forall i:word :: eehci_valid_slot_id(i)
    ==> eehci_mem_get_eehci_id(va_get_globals(va_s0), i) != eehci_idword)) && (ret == TRUE ==>
    pids_is_existing_wimp_pid(va_get_globals(va_s0), new_pid))) && (ret == TRUE ==> eehci_idword !=
    eEHCI_ID_INVALID)) && (ret == TRUE ==> (var eehci_id:Dev_ID :=
    Map_EEHCIIDWord_ToDevID(va_s0.subjects, va_s0.objects, va_s0.id_mappings, eehci_idword);
    eehci_id in va_s0.subjects.eehcis))) && (ret == TRUE ==> eehci_valid_slot_id(eehci_slot))) &&
    (ret == TRUE ==> eechi_activate_globalvars_relation(va_get_globals(va_s0),
    va_get_globals(va_sM), eehci_slot, eehci_idword, eehci_handle, new_pid))) && (ret != TRUE ==>
    global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM)))
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
  reveal_va_code_EEHCI_Activate_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_ffi_eehci_activate_stack_and_globals();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b4, va_s4, va_sM);
  ghost var va_b11, va_s11 := va_lemma_PUSH_VOID(va_b10, va_s10, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_PUSH(va_b12, va_s12, va_sM, va_op_word_reg(ECX));
  ghost var new_pid := va_get_reg(ECX, va_s13);
  ghost var va_b15, va_s15 := va_lemma_pids_is_existing_wimp_pid(va_b13, va_s13, va_sM);
  ghost var va_b16, va_s16 := va_lemma_Load(va_b15, va_s15, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0);
  ghost var va_b17, va_s17 := va_lemma_POP_VOID(va_b16, va_s16, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_sM);
  ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
    va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
  if (va_cond_c18)
  {
    ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
    assert pids_is_existing_wimp_pid(va_get_globals(va_s19), new_pid);  // line 107 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    ghost var old_globals := va_get_globals(va_s19);
    assert old_globals == va_get_globals(va_old_s);  // line 110 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    ghost var va_b24, va_s24 := va_lemma_PUSH_VOID(va_b20, va_s19, va_s18, 4 * ARCH_WORD_BYTES);
    ghost var va_b25, va_s25 := va_lemma_CALL_EEHCI_Activate(va_b24, va_s24, va_s18);
    ghost var va_b26, va_s26 := va_lemma_Load(va_b25, va_s25, va_s18, va_op_word_reg(EAX),
      va_op_word_reg(ESP), 0);
    ghost var va_b27, va_s27 := va_lemma_Load(va_b26, va_s26, va_s18, va_op_word_reg(ESI),
      va_op_word_reg(ESP), 1 * ARCH_WORD_BYTES);
    ghost var va_b28, va_s28 := va_lemma_Load(va_b27, va_s27, va_s18, va_op_word_reg(EDI),
      va_op_word_reg(ESP), 2 * ARCH_WORD_BYTES);
    ghost var va_b29, va_s29 := va_lemma_Load(va_b28, va_s28, va_s18, va_op_word_reg(EDX),
      va_op_word_reg(ESP), 3 * ARCH_WORD_BYTES);
    ghost var va_b30, va_s30 := va_lemma_POP_VOID(va_b29, va_s29, va_s18, 4 * ARCH_WORD_BYTES);
    ghost var va_s31, va_c31, va_b31 := va_lemma_block(va_b30, va_s30, va_s18);
    ghost var va_cond_c31, va_s32:va_state := va_lemma_ifElse(va_get_ifCond(va_c31),
      va_get_ifTrue(va_c31), va_get_ifFalse(va_c31), va_s30, va_s31);
    if (va_cond_c31)
    {
      ghost var va_b33 := va_get_block(va_get_ifTrue(va_c31));
      ghost var globals1 := va_get_globals(va_s32);
      assert va_get_reg(ESI, va_s32) != eEHCI_ID_INVALID;  // line 124 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      assert ffi_eehci_activate_globals_relationship(old_globals, globals1, va_get_reg(EDI,
        va_s32), va_get_reg(ESI, va_s32), va_get_reg(EDX, va_s32), TRUE);  // line 125 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_ffi_eehci_activate_globals_relationship_Property(old_globals, globals1, va_get_reg(EDI,
        va_s32), va_get_reg(ESI, va_s32), va_get_reg(EDX, va_s32), TRUE);
      Lemma_OSSubjsHaveUnchangedPIDs_IfSubjectsAreSame(va_old_s, va_s32);
      ghost var va_b39, va_s39 := va_lemma_Load(va_b33, va_s32, va_s31, va_op_word_reg(ECX),
        va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
      ghost var va_b40, va_s40 := va_lemma_PUSH(va_b39, va_s39, va_s31, va_op_word_reg(ECX));
      assert va_get_reg(ECX, va_s40) == new_pid;  // line 134 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      ghost var va_b42, va_s42 := va_lemma_PUSH(va_b40, va_s40, va_s31, va_const_word(0));
      ghost var va_b43, va_s43 := va_lemma_PUSH(va_b42, va_s42, va_s31, va_op_word_reg(EDI));
      ghost var va_b44, va_s44 := va_lemma__eehci_info_update_slot_to_valid_pid(va_b43, va_s43,
        va_s31);
      ghost var va_b45, va_s45 := va_lemma_POP_VOID(va_b44, va_s44, va_s31, 3 * ARCH_WORD_BYTES);
      assert eehci_info_only_change_slot_newvalue(globals1, va_get_globals(va_s45), va_get_reg(EDI,
        va_s45), 0, new_pid);  // line 140 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      ghost var va_b47, va_s47 := va_lemma_Store(va_b45, va_s45, va_s31, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      ghost var va_b48, va_s48 := va_lemma_Store(va_b47, va_s47, va_s31, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_op_word_reg(ESI));
      ghost var va_b49, va_s49 := va_lemma_Store(va_b48, va_s48, va_s31, va_op_word_reg(EBP), 3 *
        ARCH_WORD_BYTES, va_op_word_reg(EDX));
      ghost var va_b50, va_s50 := va_lemma_Store(va_b49, va_s49, va_s31, va_op_word_reg(EBP), 4 *
        ARCH_WORD_BYTES, va_op_word_reg(EDI));
      Lemma_EEHCI_Activate_ProveProperty2(old_globals, globals1, va_get_globals(va_s50),
        va_get_reg(EDI, va_s50), va_get_reg(ESI, va_s50), va_get_reg(EDX, va_s50), new_pid);
      va_s31 := va_lemma_empty(va_s50, va_s31);
    }
    else
    {
      ghost var va_b52 := va_get_block(va_get_ifFalse(va_c31));
      ghost var va_b53, va_s53 := va_lemma_Store(va_b52, va_s32, va_s31, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b54, va_s54 := va_lemma_Store(va_b53, va_s53, va_s31, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_const_word(eEHCI_ID_INVALID));
      ghost var va_b55, va_s55 := va_lemma_Store(va_b54, va_s54, va_s31, va_op_word_reg(EBP), 3 *
        ARCH_WORD_BYTES, va_const_word(eEHCI_Handle_INVALID));
      ghost var va_b56, va_s56 := va_lemma_Store(va_b55, va_s55, va_s31, va_op_word_reg(EBP), 4 *
        ARCH_WORD_BYTES, va_const_word(eEHCI_SlotID_EMPTY));
      assert va_get_globals(va_s56) == va_get_globals(va_old_s);  // line 156 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s56));
      va_s31 := va_lemma_empty(va_s56, va_s31);
    }
    va_s18 := va_lemma_empty(va_s31, va_s18);
  }
  else
  {
    ghost var va_b59 := va_get_block(va_get_ifFalse(va_c18));
    ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s19, va_s18, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b61, va_s61 := va_lemma_Store(va_b60, va_s60, va_s18, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(eEHCI_ID_INVALID));
    ghost var va_b62, va_s62 := va_lemma_Store(va_b61, va_s61, va_s18, va_op_word_reg(EBP), 3 *
      ARCH_WORD_BYTES, va_const_word(eEHCI_Handle_INVALID));
    ghost var va_b63, va_s63 := va_lemma_Store(va_b62, va_s62, va_s18, va_op_word_reg(EBP), 4 *
      ARCH_WORD_BYTES, va_const_word(eEHCI_SlotID_EMPTY));
    assert va_get_globals(va_s63) == va_get_globals(va_old_s);  // line 167 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s63));
    va_s18 := va_lemma_empty(va_s63, va_s18);
  }
  ghost var va_b66, va_s66 := va_lemma_POP_Reg1ToReg6(va_b18, va_s18, va_sM);
  ghost var va_b67, va_s67 := va_lemma_POP_OneReg(va_b66, va_s66, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s67, va_sM);
}
//--
//-- EEHCI_Deactivate_Impl

function method{:opaque} va_code_EEHCI_Deactivate_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_eehci_check_slot_id(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_eehci_mem_usbtd_reg_find_nonempty_slot(va_op_reg_reg(EAX), va_op_reg_reg(EBX),
    va_op_reg_reg(ECX)), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_PUSH(va_const_word(PID_INVALID)),
    va_CCons(va_code_PUSH(va_const_word(0)), va_CCons(va_code_Load(va_op_word_reg(EAX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code__eehci_info_update_slot_to_invalid_pid(), va_CCons(va_code_POP_VOID(3 *
    ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(EBP), 1 *
    ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_CALL_EEHCI_Deactivate(), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil())))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))
}

lemma{:timeLimitMultiplier 20} va_lemma_EEHCI_Deactivate_Impl(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_EEHCI_Deactivate_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ +
    FFI_EEHCI_Deactivate_StackParamsWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space) && (var stack_params_space := 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); (((ret == TRUE ==>
    eehci_valid_slot_id(eehci_slot)) && (ret == TRUE ==>
    pids_is_existing_wimp_pid(va_get_globals(va_s0), eehci_info_get_pid(va_get_globals(va_s0),
    eehci_slot).v))) && (ret == TRUE ==>
    eechi_deactivate_globalvars_relation(va_get_globals(va_s0), va_get_globals(va_sM),
    eehci_slot))) && (ret != TRUE ==>
    global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM)))
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
  reveal_va_code_EEHCI_Deactivate_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_ffi_eehci_deactivate_stack_and_globals();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_Reg1ToReg6(va_b4, va_s4, va_sM);
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var eehci_slot := va_get_reg(EBX, va_s10);
  ghost var va_b12, va_s12 := va_lemma_eehci_check_slot_id(va_b10, va_s10, va_sM,
    va_op_reg_reg(EBX), va_op_reg_reg(EAX));
  ghost var va_s13, va_c13, va_b13 := va_lemma_block(va_b12, va_s12, va_sM);
  ghost var va_cond_c13, va_s14:va_state := va_lemma_ifElse(va_get_ifCond(va_c13),
    va_get_ifTrue(va_c13), va_get_ifFalse(va_c13), va_s12, va_s13);
  if (va_cond_c13)
  {
    ghost var va_b15 := va_get_block(va_get_ifTrue(va_c13));
    ghost var va_b16, va_s16 := va_lemma_Load(va_b15, va_s14, va_s13, va_op_word_reg(EAX),
      va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
    ghost var va_b17, va_s17 := va_lemma_PUSH_VOID(va_b16, va_s16, va_s13, 1 * ARCH_WORD_BYTES);
    ghost var va_b18, va_s18 := va_lemma_eehci_info_get_pid(va_b17, va_s17, va_s13,
      va_op_reg_reg(EAX));
    ghost var va_b19, va_s19 := va_lemma_Load(va_b18, va_s18, va_s13, va_op_word_reg(EBX),
      va_op_word_reg(ESP), 0);
    ghost var va_b20, va_s20 := va_lemma_POP_VOID(va_b19, va_s19, va_s13, 1 * ARCH_WORD_BYTES);
    ghost var va_b21, va_s21 := va_lemma_PUSH_VOID(va_b20, va_s20, va_s13, 1 * ARCH_WORD_BYTES);
    ghost var va_b22, va_s22 := va_lemma_PUSH(va_b21, va_s21, va_s13, va_op_word_reg(EBX));
    ghost var va_b23, va_s23 := va_lemma_pids_is_existing_wimp_pid(va_b22, va_s22, va_s13);
    ghost var va_b24, va_s24 := va_lemma_Load(va_b23, va_s23, va_s13, va_op_word_reg(EDX),
      va_op_word_reg(ESP), 0);
    ghost var va_b25, va_s25 := va_lemma_POP_VOID(va_b24, va_s24, va_s13, 2 * ARCH_WORD_BYTES);
    ghost var va_s26, va_c26, va_b26 := va_lemma_block(va_b25, va_s25, va_s13);
    ghost var va_cond_c26, va_s27:va_state := va_lemma_ifElse(va_get_ifCond(va_c26),
      va_get_ifTrue(va_c26), va_get_ifFalse(va_c26), va_s25, va_s26);
    if (va_cond_c26)
    {
      ghost var va_b28 := va_get_block(va_get_ifTrue(va_c26));
      ghost var va_b29, va_s29 := va_lemma_Load(va_b28, va_s27, va_s26, va_op_word_reg(EAX),
        va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
      ghost var va_b30, va_s30 := va_lemma_eehci_mem_usbtd_reg_find_nonempty_slot(va_b29, va_s29,
        va_s26, va_op_reg_reg(EAX), va_op_reg_reg(EBX), va_op_reg_reg(ECX));
      ghost var va_s31, va_c31, va_b31 := va_lemma_block(va_b30, va_s30, va_s26);
      ghost var va_cond_c31, va_s32:va_state := va_lemma_ifElse(va_get_ifCond(va_c31),
        va_get_ifTrue(va_c31), va_get_ifFalse(va_c31), va_s30, va_s31);
      if (va_cond_c31)
      {
        ghost var va_b33 := va_get_block(va_get_ifTrue(va_c31));
        ghost var old_globals := va_get_globals(va_s32);
        assert old_globals == va_get_globals(va_old_s);  // line 264 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        assert EECHI_DoNotRefAnyUSBTD(va_get_globals(va_s32), eehci_slot);  // line 265 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        ghost var va_b37, va_s37 := va_lemma_PUSH(va_b33, va_s32, va_s31,
          va_const_word(PID_INVALID));
        ghost var va_b38, va_s38 := va_lemma_PUSH(va_b37, va_s37, va_s31, va_const_word(0));
        ghost var va_b39, va_s39 := va_lemma_Load(va_b38, va_s38, va_s31, va_op_word_reg(EAX),
          va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
        ghost var va_b40, va_s40 := va_lemma_PUSH(va_b39, va_s39, va_s31, va_op_word_reg(EAX));
        ghost var va_b41, va_s41 := va_lemma__eehci_info_update_slot_to_invalid_pid(va_b40, va_s40,
          va_s31);
        ghost var va_b42, va_s42 := va_lemma_POP_VOID(va_b41, va_s41, va_s31, 3 * ARCH_WORD_BYTES);
        ghost var globals1 := va_get_globals(va_s42);
        assert eehci_info_only_change_slot_newvalue(old_globals, globals1, eehci_slot, 0,
          PID_INVALID);  // line 276 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        assert va_get_reg(ESP, va_s42) == va_get_reg(ESP, va_old_s) - 7 * ARCH_WORD_BYTES;  // line 279 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        ghost var va_b46, va_s46 := va_lemma_Load(va_b42, va_s42, va_s31, va_op_word_reg(EAX),
          va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
        ghost var va_b47, va_s47 := va_lemma_PUSH(va_b46, va_s46, va_s31, va_op_word_reg(EAX));
        ghost var va_b48, va_s48 := va_lemma_CALL_EEHCI_Deactivate(va_b47, va_s47, va_s31);
        ghost var va_b49, va_s49 := va_lemma_POP_VOID(va_b48, va_s48, va_s31, 1 * ARCH_WORD_BYTES);
        assert ffi_eehci_deactivate_globals_relationship(globals1, va_get_globals(va_s49),
          eehci_slot);  // line 285 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        Lemma_EEHCI_Deactivate_ProveProperty2(old_globals, globals1, va_get_globals(va_s49),
          eehci_slot);
        ghost var va_b52, va_s52 := va_lemma_Store(va_b49, va_s49, va_s31, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(TRUE));
        va_s31 := va_lemma_empty(va_s52, va_s31);
      }
      else
      {
        ghost var va_b53 := va_get_block(va_get_ifFalse(va_c31));
        ghost var va_b54, va_s54 := va_lemma_Store(va_b53, va_s32, va_s31, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s54) == va_get_globals(va_old_s);  // line 295 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s54));
        va_s31 := va_lemma_empty(va_s54, va_s31);
      }
      va_s26 := va_lemma_empty(va_s31, va_s26);
    }
    else
    {
      ghost var va_b57 := va_get_block(va_get_ifFalse(va_c26));
      ghost var va_b58, va_s58 := va_lemma_Store(va_b57, va_s27, va_s26, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s58) == va_get_globals(va_old_s);  // line 303 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s58));
      va_s26 := va_lemma_empty(va_s58, va_s26);
    }
    va_s13 := va_lemma_empty(va_s26, va_s13);
  }
  else
  {
    ghost var va_b61 := va_get_block(va_get_ifFalse(va_c13));
    ghost var va_b62, va_s62 := va_lemma_Store(va_b61, va_s14, va_s13, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s62) == va_get_globals(va_old_s);  // line 311 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s62));
    va_s13 := va_lemma_empty(va_s62, va_s13);
  }
  ghost var va_b65, va_s65 := va_lemma_POP_Reg1ToReg6(va_b13, va_s13, va_sM);
  ghost var va_b66, va_s66 := va_lemma_POP_OneReg(va_b65, va_s65, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s66, va_sM);
}
//--
//-- WimpDrv_Write_eEHCI_Config_Impl

function method{:opaque} va_code_WimpDrv_Write_eEHCI_Config_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_eehci_check_slot_id(va_op_reg_reg(ECX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_op_word_reg(ECX)), va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_eehci_write_config(), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 15} va_lemma_WimpDrv_Write_eEHCI_Config_Impl(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Write_eEHCI_Config_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2
    * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    ((((((ret == TRUE ==> wimpdrv_valid_slot_id(wimpdrv_slot)) && (ret == TRUE ==>
    eehci_valid_slot_id(eehci_slot))) && (ret == TRUE ==> wimpdrv_get_pid(va_get_globals(va_s0),
    wimpdrv_slot) in pids_parse_g_wimp_pids(va_get_globals(va_s0)))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot) ==
    eehci_info_get_pid(va_get_globals(va_s0), eehci_slot))) && (ret == TRUE ==> (var vaddr :=
    AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES +
    G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset; va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_EEHCI_MEM(), vaddr, new_v)))) && (ret != TRUE ==>
    global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM)))) &&
    (ret != TRUE ==> state_equal_except_mstate(va_s0, va_sM))
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
  reveal_va_code_WimpDrv_Write_eEHCI_Config_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_wimpdrv_check_slotid(va_b12, va_s12, va_sM,
    va_op_reg_reg(EBX), va_op_reg_reg(EAX));
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_eehci_check_slot_id(va_b16, va_s15, va_s14,
      va_op_reg_reg(ECX), va_op_reg_reg(EAX));
    ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_s14);
    ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
      va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
    if (va_cond_c18)
    {
      ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
      ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s19, va_s18, va_op_word_reg(EBX));
      ghost var va_b22, va_s22 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b21, va_s21, va_s18);
      ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s18, va_op_word_reg(EDI),
        va_op_word_reg(ESP), 0);
      ghost var va_b24, va_s24 := va_lemma_POP_VOID(va_b23, va_s23, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b25, va_s25 := va_lemma_PUSH_VOID(va_b24, va_s24, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s25, va_s18, va_op_reg_reg(EAX),
        va_op_word_reg(ECX));
      ghost var va_b27, va_s27 := va_lemma_eehci_info_get_pid(va_b26, va_s26, va_s18,
        va_op_reg_reg(EAX));
      ghost var va_b28, va_s28 := va_lemma_Load(va_b27, va_s27, va_s18, va_op_word_reg(ESI),
        va_op_word_reg(ESP), 0);
      ghost var va_b29, va_s29 := va_lemma_POP_VOID(va_b28, va_s28, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b30, va_s30 := va_lemma_PUSH_VOID(va_b29, va_s29, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b31, va_s31 := va_lemma_PUSH(va_b30, va_s30, va_s18, va_op_word_reg(EDI));
      ghost var va_b32, va_s32 := va_lemma_pids_is_existing_wimp_pid(va_b31, va_s31, va_s18);
      ghost var va_b33, va_s33 := va_lemma_Load(va_b32, va_s32, va_s18, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b34, va_s34 := va_lemma_POP_VOID(va_b33, va_s33, va_s18, 2 * ARCH_WORD_BYTES);
      ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b34, va_s34, va_s18);
      ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
        va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s34, va_s35);
      if (va_cond_c35)
      {
        ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
        ghost var va_s38, va_c38, va_b38 := va_lemma_block(va_b37, va_s36, va_s35);
        ghost var va_cond_c38, va_s39:va_state := va_lemma_ifElse(va_get_ifCond(va_c38),
          va_get_ifTrue(va_c38), va_get_ifFalse(va_c38), va_s36, va_s38);
        if (va_cond_c38)
        {
          ghost var va_b40 := va_get_block(va_get_ifTrue(va_c38));
          ghost var va_b41, va_s41 := va_lemma_Load(va_b40, va_s39, va_s38, va_op_word_reg(EDX),
            va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
          ghost var va_b42, va_s42 := va_lemma_PUSH(va_b41, va_s41, va_s38, va_op_word_reg(EDX));
          ghost var va_b43, va_s43 := va_lemma_PUSH(va_b42, va_s42, va_s38, va_op_word_reg(ECX));
          ghost var va_b44, va_s44 := va_lemma_eehci_write_config(va_b43, va_s43, va_s38);
          ghost var va_b45, va_s45 := va_lemma_POP_VOID(va_b44, va_s44, va_s38, 2 *
            ARCH_WORD_BYTES);
          ghost var va_b46, va_s46 := va_lemma_Store(va_b45, va_s45, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          va_s38 := va_lemma_empty(va_s46, va_s38);
        }
        else
        {
          ghost var va_b47 := va_get_block(va_get_ifFalse(va_c38));
          ghost var va_b48, va_s48 := va_lemma_Store(va_b47, va_s39, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s48) == va_get_globals(va_old_s);  // line 434 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s48));
          va_s38 := va_lemma_empty(va_s48, va_s38);
        }
        va_s35 := va_lemma_empty(va_s38, va_s35);
      }
      else
      {
        ghost var va_b51 := va_get_block(va_get_ifFalse(va_c35));
        ghost var va_b52, va_s52 := va_lemma_Store(va_b51, va_s36, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s52) == va_get_globals(va_old_s);  // line 442 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s52));
        va_s35 := va_lemma_empty(va_s52, va_s35);
      }
      va_s18 := va_lemma_empty(va_s35, va_s18);
    }
    else
    {
      ghost var va_b55 := va_get_block(va_get_ifFalse(va_c18));
      ghost var va_b56, va_s56 := va_lemma_Store(va_b55, va_s19, va_s18, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s56) == va_get_globals(va_old_s);  // line 450 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s56));
      va_s18 := va_lemma_empty(va_s56, va_s18);
    }
    va_s14 := va_lemma_empty(va_s18, va_s14);
  }
  else
  {
    ghost var va_b59 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s60) == va_get_globals(va_old_s);  // line 458 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s60));
    va_s14 := va_lemma_empty(va_s60, va_s14);
  }
  ghost var va_b63, va_s63 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b64, va_s64 := va_lemma_POP_OneReg(va_b63, va_s63, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s64, va_sM);
}
//--
//-- WimpDrv_Read_eEHCI_Config_Impl

function method{:opaque} va_code_WimpDrv_Read_eEHCI_Config_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_eehci_check_slot_id(va_op_reg_reg(ECX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_op_word_reg(ECX)), va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(ECX)), va_CCons(va_code_eehci_read_config(),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EDX)), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 15} va_lemma_WimpDrv_Read_eEHCI_Config_Impl(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Read_eEHCI_Config_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    val:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES);
    ((((((ret == TRUE ==> wimpdrv_valid_slot_id(wimpdrv_slot)) && (ret == TRUE ==>
    eehci_valid_slot_id(eehci_slot))) && (ret == TRUE ==> wimpdrv_get_pid(va_get_globals(va_s0),
    wimpdrv_slot) in pids_parse_g_wimp_pids(va_get_globals(va_s0)))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot) ==
    eehci_info_get_pid(va_get_globals(va_s0), eehci_slot))) && (ret == TRUE ==>
    eehci_mem_get_config_reg(va_get_globals(va_s0), eehci_slot) == val)) &&
    global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM))) &&
    state_equal_except_mstate(va_s0, va_sM)
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
  reveal_va_code_WimpDrv_Read_eEHCI_Config_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_wimpdrv_check_slotid(va_b12, va_s12, va_sM,
    va_op_reg_reg(EBX), va_op_reg_reg(EAX));
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_eehci_check_slot_id(va_b16, va_s15, va_s14,
      va_op_reg_reg(ECX), va_op_reg_reg(EAX));
    ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_s14);
    ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
      va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
    if (va_cond_c18)
    {
      ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
      ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s19, va_s18, va_op_word_reg(EBX));
      ghost var va_b22, va_s22 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b21, va_s21, va_s18);
      ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s18, va_op_word_reg(EDI),
        va_op_word_reg(ESP), 0);
      ghost var va_b24, va_s24 := va_lemma_POP_VOID(va_b23, va_s23, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b25, va_s25 := va_lemma_PUSH_VOID(va_b24, va_s24, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s25, va_s18, va_op_reg_reg(EAX),
        va_op_word_reg(ECX));
      ghost var va_b27, va_s27 := va_lemma_eehci_info_get_pid(va_b26, va_s26, va_s18,
        va_op_reg_reg(EAX));
      ghost var va_b28, va_s28 := va_lemma_Load(va_b27, va_s27, va_s18, va_op_word_reg(ESI),
        va_op_word_reg(ESP), 0);
      ghost var va_b29, va_s29 := va_lemma_POP_VOID(va_b28, va_s28, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b30, va_s30 := va_lemma_PUSH_VOID(va_b29, va_s29, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b31, va_s31 := va_lemma_PUSH(va_b30, va_s30, va_s18, va_op_word_reg(EDI));
      ghost var va_b32, va_s32 := va_lemma_pids_is_existing_wimp_pid(va_b31, va_s31, va_s18);
      ghost var va_b33, va_s33 := va_lemma_Load(va_b32, va_s32, va_s18, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b34, va_s34 := va_lemma_POP_VOID(va_b33, va_s33, va_s18, 2 * ARCH_WORD_BYTES);
      ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b34, va_s34, va_s18);
      ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
        va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s34, va_s35);
      if (va_cond_c35)
      {
        ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
        ghost var va_s38, va_c38, va_b38 := va_lemma_block(va_b37, va_s36, va_s35);
        ghost var va_cond_c38, va_s39:va_state := va_lemma_ifElse(va_get_ifCond(va_c38),
          va_get_ifTrue(va_c38), va_get_ifFalse(va_c38), va_s36, va_s38);
        if (va_cond_c38)
        {
          ghost var va_b40 := va_get_block(va_get_ifTrue(va_c38));
          ghost var va_b41, va_s41 := va_lemma_PUSH(va_b40, va_s39, va_s38, va_op_word_reg(ECX));
          ghost var va_b42, va_s42 := va_lemma_eehci_read_config(va_b41, va_s41, va_s38);
          ghost var va_b43, va_s43 := va_lemma_Load(va_b42, va_s42, va_s38, va_op_word_reg(EDX),
            va_op_word_reg(ESP), 0);
          ghost var va_b44, va_s44 := va_lemma_POP_VOID(va_b43, va_s43, va_s38, 1 *
            ARCH_WORD_BYTES);
          ghost var va_b45, va_s45 := va_lemma_Store(va_b44, va_s44, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          ghost var va_b46, va_s46 := va_lemma_Store(va_b45, va_s45, va_s38, va_op_word_reg(EBP), 2
            * ARCH_WORD_BYTES, va_op_word_reg(EDX));
          assert va_get_globals(va_s46) == va_get_globals(va_old_s);  // line 570 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s46));
          va_s38 := va_lemma_empty(va_s46, va_s38);
        }
        else
        {
          ghost var va_b49 := va_get_block(va_get_ifFalse(va_c38));
          ghost var va_b50, va_s50 := va_lemma_Store(va_b49, va_s39, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s50) == va_get_globals(va_old_s);  // line 577 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s50));
          va_s38 := va_lemma_empty(va_s50, va_s38);
        }
        va_s35 := va_lemma_empty(va_s38, va_s35);
      }
      else
      {
        ghost var va_b53 := va_get_block(va_get_ifFalse(va_c35));
        ghost var va_b54, va_s54 := va_lemma_Store(va_b53, va_s36, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s54) == va_get_globals(va_old_s);  // line 585 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s54));
        va_s35 := va_lemma_empty(va_s54, va_s35);
      }
      va_s18 := va_lemma_empty(va_s35, va_s18);
    }
    else
    {
      ghost var va_b57 := va_get_block(va_get_ifFalse(va_c18));
      ghost var va_b58, va_s58 := va_lemma_Store(va_b57, va_s19, va_s18, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s58) == va_get_globals(va_old_s);  // line 593 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s58));
      va_s18 := va_lemma_empty(va_s58, va_s18);
    }
    va_s14 := va_lemma_empty(va_s18, va_s14);
  }
  else
  {
    ghost var va_b61 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b62, va_s62 := va_lemma_Store(va_b61, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s62) == va_get_globals(va_old_s);  // line 601 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s62));
    va_s14 := va_lemma_empty(va_s62, va_s14);
  }
  ghost var va_b65, va_s65 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b66, va_s66 := va_lemma_POP_OneReg(va_b65, va_s65, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s66, va_sM);
}
//--
//-- WimpDrv_Write_eEHCI_Status_Impl

function method{:opaque} va_code_WimpDrv_Write_eEHCI_Status_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_eehci_check_slot_id(va_op_reg_reg(ECX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_op_word_reg(ECX)), va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_eehci_write_status(), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 15} va_lemma_WimpDrv_Write_eEHCI_Status_Impl(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Write_eEHCI_Status_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2
    * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    ((((((ret == TRUE ==> wimpdrv_valid_slot_id(wimpdrv_slot)) && (ret == TRUE ==>
    eehci_valid_slot_id(eehci_slot))) && (ret == TRUE ==> wimpdrv_get_pid(va_get_globals(va_s0),
    wimpdrv_slot) in pids_parse_g_wimp_pids(va_get_globals(va_s0)))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot) ==
    eehci_info_get_pid(va_get_globals(va_s0), eehci_slot))) && (ret == TRUE ==> (var vaddr :=
    AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES +
    G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset; va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_EEHCI_MEM(), vaddr, new_v)))) && (ret != TRUE ==>
    global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM)))) &&
    (ret != TRUE ==> state_equal_except_mstate(va_s0, va_sM))
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
  reveal_va_code_WimpDrv_Write_eEHCI_Status_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_wimpdrv_check_slotid(va_b12, va_s12, va_sM,
    va_op_reg_reg(EBX), va_op_reg_reg(EAX));
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_eehci_check_slot_id(va_b16, va_s15, va_s14,
      va_op_reg_reg(ECX), va_op_reg_reg(EAX));
    ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_s14);
    ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
      va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
    if (va_cond_c18)
    {
      ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
      ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s19, va_s18, va_op_word_reg(EBX));
      ghost var va_b22, va_s22 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b21, va_s21, va_s18);
      ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s18, va_op_word_reg(EDI),
        va_op_word_reg(ESP), 0);
      ghost var va_b24, va_s24 := va_lemma_POP_VOID(va_b23, va_s23, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b25, va_s25 := va_lemma_PUSH_VOID(va_b24, va_s24, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s25, va_s18, va_op_reg_reg(EAX),
        va_op_word_reg(ECX));
      ghost var va_b27, va_s27 := va_lemma_eehci_info_get_pid(va_b26, va_s26, va_s18,
        va_op_reg_reg(EAX));
      ghost var va_b28, va_s28 := va_lemma_Load(va_b27, va_s27, va_s18, va_op_word_reg(ESI),
        va_op_word_reg(ESP), 0);
      ghost var va_b29, va_s29 := va_lemma_POP_VOID(va_b28, va_s28, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b30, va_s30 := va_lemma_PUSH_VOID(va_b29, va_s29, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b31, va_s31 := va_lemma_PUSH(va_b30, va_s30, va_s18, va_op_word_reg(EDI));
      ghost var va_b32, va_s32 := va_lemma_pids_is_existing_wimp_pid(va_b31, va_s31, va_s18);
      ghost var va_b33, va_s33 := va_lemma_Load(va_b32, va_s32, va_s18, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b34, va_s34 := va_lemma_POP_VOID(va_b33, va_s33, va_s18, 2 * ARCH_WORD_BYTES);
      ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b34, va_s34, va_s18);
      ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
        va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s34, va_s35);
      if (va_cond_c35)
      {
        ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
        ghost var va_s38, va_c38, va_b38 := va_lemma_block(va_b37, va_s36, va_s35);
        ghost var va_cond_c38, va_s39:va_state := va_lemma_ifElse(va_get_ifCond(va_c38),
          va_get_ifTrue(va_c38), va_get_ifFalse(va_c38), va_s36, va_s38);
        if (va_cond_c38)
        {
          ghost var va_b40 := va_get_block(va_get_ifTrue(va_c38));
          ghost var va_b41, va_s41 := va_lemma_Load(va_b40, va_s39, va_s38, va_op_word_reg(EDX),
            va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
          ghost var va_b42, va_s42 := va_lemma_PUSH(va_b41, va_s41, va_s38, va_op_word_reg(EDX));
          ghost var va_b43, va_s43 := va_lemma_PUSH(va_b42, va_s42, va_s38, va_op_word_reg(ECX));
          ghost var va_b44, va_s44 := va_lemma_eehci_write_status(va_b43, va_s43, va_s38);
          ghost var va_b45, va_s45 := va_lemma_POP_VOID(va_b44, va_s44, va_s38, 2 *
            ARCH_WORD_BYTES);
          ghost var va_b46, va_s46 := va_lemma_Store(va_b45, va_s45, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          va_s38 := va_lemma_empty(va_s46, va_s38);
        }
        else
        {
          ghost var va_b47 := va_get_block(va_get_ifFalse(va_c38));
          ghost var va_b48, va_s48 := va_lemma_Store(va_b47, va_s39, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s48) == va_get_globals(va_old_s);  // line 724 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s48));
          va_s38 := va_lemma_empty(va_s48, va_s38);
        }
        va_s35 := va_lemma_empty(va_s38, va_s35);
      }
      else
      {
        ghost var va_b51 := va_get_block(va_get_ifFalse(va_c35));
        ghost var va_b52, va_s52 := va_lemma_Store(va_b51, va_s36, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s52) == va_get_globals(va_old_s);  // line 732 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s52));
        va_s35 := va_lemma_empty(va_s52, va_s35);
      }
      va_s18 := va_lemma_empty(va_s35, va_s18);
    }
    else
    {
      ghost var va_b55 := va_get_block(va_get_ifFalse(va_c18));
      ghost var va_b56, va_s56 := va_lemma_Store(va_b55, va_s19, va_s18, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s56) == va_get_globals(va_old_s);  // line 740 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s56));
      va_s18 := va_lemma_empty(va_s56, va_s18);
    }
    va_s14 := va_lemma_empty(va_s18, va_s14);
  }
  else
  {
    ghost var va_b59 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s60) == va_get_globals(va_old_s);  // line 748 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s60));
    va_s14 := va_lemma_empty(va_s60, va_s14);
  }
  ghost var va_b63, va_s63 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b64, va_s64 := va_lemma_POP_OneReg(va_b63, va_s63, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s64, va_sM);
}
//--
//-- WimpDrv_Read_eEHCI_Status_Impl

function method{:opaque} va_code_WimpDrv_Read_eEHCI_Status_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_eehci_check_slot_id(va_op_reg_reg(ECX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_op_word_reg(ECX)), va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(ECX)), va_CCons(va_code_eehci_read_status(),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EDX)), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 15} va_lemma_WimpDrv_Read_eEHCI_Status_Impl(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Read_eEHCI_Status_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    val:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES);
    ((((((ret == TRUE ==> wimpdrv_valid_slot_id(wimpdrv_slot)) && (ret == TRUE ==>
    eehci_valid_slot_id(eehci_slot))) && (ret == TRUE ==> wimpdrv_get_pid(va_get_globals(va_s0),
    wimpdrv_slot) in pids_parse_g_wimp_pids(va_get_globals(va_s0)))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot) ==
    eehci_info_get_pid(va_get_globals(va_s0), eehci_slot))) && (ret == TRUE ==>
    eehci_mem_get_status_reg(va_get_globals(va_s0), eehci_slot) == val)) &&
    global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM))) &&
    state_equal_except_mstate(va_s0, va_sM)
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
  reveal_va_code_WimpDrv_Read_eEHCI_Status_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_wimpdrv_check_slotid(va_b12, va_s12, va_sM,
    va_op_reg_reg(EBX), va_op_reg_reg(EAX));
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_eehci_check_slot_id(va_b16, va_s15, va_s14,
      va_op_reg_reg(ECX), va_op_reg_reg(EAX));
    ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_s14);
    ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
      va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
    if (va_cond_c18)
    {
      ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
      ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s19, va_s18, va_op_word_reg(EBX));
      ghost var va_b22, va_s22 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b21, va_s21, va_s18);
      ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s18, va_op_word_reg(EDI),
        va_op_word_reg(ESP), 0);
      ghost var va_b24, va_s24 := va_lemma_POP_VOID(va_b23, va_s23, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b25, va_s25 := va_lemma_PUSH_VOID(va_b24, va_s24, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s25, va_s18, va_op_reg_reg(EAX),
        va_op_word_reg(ECX));
      ghost var va_b27, va_s27 := va_lemma_eehci_info_get_pid(va_b26, va_s26, va_s18,
        va_op_reg_reg(EAX));
      ghost var va_b28, va_s28 := va_lemma_Load(va_b27, va_s27, va_s18, va_op_word_reg(ESI),
        va_op_word_reg(ESP), 0);
      ghost var va_b29, va_s29 := va_lemma_POP_VOID(va_b28, va_s28, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b30, va_s30 := va_lemma_PUSH_VOID(va_b29, va_s29, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b31, va_s31 := va_lemma_PUSH(va_b30, va_s30, va_s18, va_op_word_reg(EDI));
      ghost var va_b32, va_s32 := va_lemma_pids_is_existing_wimp_pid(va_b31, va_s31, va_s18);
      ghost var va_b33, va_s33 := va_lemma_Load(va_b32, va_s32, va_s18, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b34, va_s34 := va_lemma_POP_VOID(va_b33, va_s33, va_s18, 2 * ARCH_WORD_BYTES);
      ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b34, va_s34, va_s18);
      ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
        va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s34, va_s35);
      if (va_cond_c35)
      {
        ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
        ghost var va_s38, va_c38, va_b38 := va_lemma_block(va_b37, va_s36, va_s35);
        ghost var va_cond_c38, va_s39:va_state := va_lemma_ifElse(va_get_ifCond(va_c38),
          va_get_ifTrue(va_c38), va_get_ifFalse(va_c38), va_s36, va_s38);
        if (va_cond_c38)
        {
          ghost var va_b40 := va_get_block(va_get_ifTrue(va_c38));
          ghost var va_b41, va_s41 := va_lemma_PUSH(va_b40, va_s39, va_s38, va_op_word_reg(ECX));
          ghost var va_b42, va_s42 := va_lemma_eehci_read_status(va_b41, va_s41, va_s38);
          ghost var va_b43, va_s43 := va_lemma_Load(va_b42, va_s42, va_s38, va_op_word_reg(EDX),
            va_op_word_reg(ESP), 0);
          ghost var va_b44, va_s44 := va_lemma_POP_VOID(va_b43, va_s43, va_s38, 1 *
            ARCH_WORD_BYTES);
          ghost var va_b45, va_s45 := va_lemma_Store(va_b44, va_s44, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          ghost var va_b46, va_s46 := va_lemma_Store(va_b45, va_s45, va_s38, va_op_word_reg(EBP), 2
            * ARCH_WORD_BYTES, va_op_word_reg(EDX));
          assert va_get_globals(va_s46) == va_get_globals(va_old_s);  // line 860 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s46));
          va_s38 := va_lemma_empty(va_s46, va_s38);
        }
        else
        {
          ghost var va_b49 := va_get_block(va_get_ifFalse(va_c38));
          ghost var va_b50, va_s50 := va_lemma_Store(va_b49, va_s39, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s50) == va_get_globals(va_old_s);  // line 867 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s50));
          va_s38 := va_lemma_empty(va_s50, va_s38);
        }
        va_s35 := va_lemma_empty(va_s38, va_s35);
      }
      else
      {
        ghost var va_b53 := va_get_block(va_get_ifFalse(va_c35));
        ghost var va_b54, va_s54 := va_lemma_Store(va_b53, va_s36, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s54) == va_get_globals(va_old_s);  // line 875 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s54));
        va_s35 := va_lemma_empty(va_s54, va_s35);
      }
      va_s18 := va_lemma_empty(va_s35, va_s18);
    }
    else
    {
      ghost var va_b57 := va_get_block(va_get_ifFalse(va_c18));
      ghost var va_b58, va_s58 := va_lemma_Store(va_b57, va_s19, va_s18, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s58) == va_get_globals(va_old_s);  // line 883 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s58));
      va_s18 := va_lemma_empty(va_s58, va_s18);
    }
    va_s14 := va_lemma_empty(va_s18, va_s14);
  }
  else
  {
    ghost var va_b61 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b62, va_s62 := va_lemma_Store(va_b61, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s62) == va_get_globals(va_old_s);  // line 891 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s62));
    va_s14 := va_lemma_empty(va_s62, va_s14);
  }
  ghost var va_b65, va_s65 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b66, va_s66 := va_lemma_POP_OneReg(va_b65, va_s65, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s66, va_sM);
}
//--
//-- WimpDrv_Write_eEHCI_IntrEnable

function method{:opaque} va_code_WimpDrv_Write_eEHCI_IntrEnable():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_eehci_check_slot_id(va_op_reg_reg(ECX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_op_word_reg(ECX)), va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(eEHCI_Intr_Disable)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_eehci_write_intr_enable(), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil()))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())))))))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 15} va_lemma_WimpDrv_Write_eEHCI_IntrEnable(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Write_eEHCI_IntrEnable(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2
    * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    ((((((ret == TRUE ==> wimpdrv_valid_slot_id(wimpdrv_slot)) && (ret == TRUE ==>
    eehci_valid_slot_id(eehci_slot))) && (ret == TRUE ==> wimpdrv_get_pid(va_get_globals(va_s0),
    wimpdrv_slot) in pids_parse_g_wimp_pids(va_get_globals(va_s0)))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot) ==
    eehci_info_get_pid(va_get_globals(va_s0), eehci_slot))) && (ret == TRUE ==> (var vaddr :=
    AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES +
    G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset; va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_EEHCI_MEM(), vaddr, new_v)))) && (ret != TRUE ==>
    global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM)))) &&
    (ret != TRUE ==> state_equal_except_mstate(va_s0, va_sM))
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
  reveal_va_code_WimpDrv_Write_eEHCI_IntrEnable();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_wimpdrv_check_slotid(va_b12, va_s12, va_sM,
    va_op_reg_reg(EBX), va_op_reg_reg(EAX));
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_eehci_check_slot_id(va_b16, va_s15, va_s14,
      va_op_reg_reg(ECX), va_op_reg_reg(EAX));
    ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_s14);
    ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
      va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
    if (va_cond_c18)
    {
      ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
      ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s19, va_s18, va_op_word_reg(EBX));
      ghost var va_b22, va_s22 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b21, va_s21, va_s18);
      ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s18, va_op_word_reg(EDI),
        va_op_word_reg(ESP), 0);
      ghost var va_b24, va_s24 := va_lemma_POP_VOID(va_b23, va_s23, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b25, va_s25 := va_lemma_PUSH_VOID(va_b24, va_s24, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s25, va_s18, va_op_reg_reg(EAX),
        va_op_word_reg(ECX));
      ghost var va_b27, va_s27 := va_lemma_eehci_info_get_pid(va_b26, va_s26, va_s18,
        va_op_reg_reg(EAX));
      ghost var va_b28, va_s28 := va_lemma_Load(va_b27, va_s27, va_s18, va_op_word_reg(ESI),
        va_op_word_reg(ESP), 0);
      ghost var va_b29, va_s29 := va_lemma_POP_VOID(va_b28, va_s28, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b30, va_s30 := va_lemma_PUSH_VOID(va_b29, va_s29, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b31, va_s31 := va_lemma_PUSH(va_b30, va_s30, va_s18, va_op_word_reg(EDI));
      ghost var va_b32, va_s32 := va_lemma_pids_is_existing_wimp_pid(va_b31, va_s31, va_s18);
      ghost var va_b33, va_s33 := va_lemma_Load(va_b32, va_s32, va_s18, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b34, va_s34 := va_lemma_POP_VOID(va_b33, va_s33, va_s18, 2 * ARCH_WORD_BYTES);
      ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b34, va_s34, va_s18);
      ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
        va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s34, va_s35);
      if (va_cond_c35)
      {
        ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
        ghost var va_s38, va_c38, va_b38 := va_lemma_block(va_b37, va_s36, va_s35);
        ghost var va_cond_c38, va_s39:va_state := va_lemma_ifElse(va_get_ifCond(va_c38),
          va_get_ifTrue(va_c38), va_get_ifFalse(va_c38), va_s36, va_s38);
        if (va_cond_c38)
        {
          ghost var va_b40 := va_get_block(va_get_ifTrue(va_c38));
          ghost var va_b41, va_s41 := va_lemma_Load(va_b40, va_s39, va_s38, va_op_word_reg(EDX),
            va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
          ghost var va_s42, va_c42, va_b42 := va_lemma_block(va_b41, va_s41, va_s38);
          ghost var va_cond_c42, va_s43:va_state := va_lemma_ifElse(va_get_ifCond(va_c42),
            va_get_ifTrue(va_c42), va_get_ifFalse(va_c42), va_s41, va_s42);
          if (va_cond_c42)
          {
            ghost var va_b44 := va_get_block(va_get_ifTrue(va_c42));
            ghost var va_b45, va_s45 := va_lemma_Load(va_b44, va_s43, va_s42, va_op_word_reg(EDX),
              va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
            ghost var va_b46, va_s46 := va_lemma_PUSH(va_b45, va_s45, va_s42, va_op_word_reg(EDX));
            ghost var va_b47, va_s47 := va_lemma_PUSH(va_b46, va_s46, va_s42, va_op_word_reg(ECX));
            ghost var va_b48, va_s48 := va_lemma_eehci_write_intr_enable(va_b47, va_s47, va_s42);
            ghost var va_b49, va_s49 := va_lemma_POP_VOID(va_b48, va_s48, va_s42, 2 *
              ARCH_WORD_BYTES);
            ghost var va_b50, va_s50 := va_lemma_Store(va_b49, va_s49, va_s42, va_op_word_reg(EBP),
              ARCH_WORD_BYTES, va_const_word(TRUE));
            va_s42 := va_lemma_empty(va_s50, va_s42);
          }
          else
          {
            ghost var va_b51 := va_get_block(va_get_ifFalse(va_c42));
            ghost var va_b52, va_s52 := va_lemma_Store(va_b51, va_s43, va_s42, va_op_word_reg(EBP),
              ARCH_WORD_BYTES, va_const_word(FALSE));
            assert va_get_globals(va_s52) == va_get_globals(va_old_s);  // line 1019 column 25 of file .\dev/usb2/eehci_ops_impl.vad
            Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
              va_get_globals(va_s52));
            va_s42 := va_lemma_empty(va_s52, va_s42);
          }
          va_s38 := va_lemma_empty(va_s42, va_s38);
        }
        else
        {
          ghost var va_b55 := va_get_block(va_get_ifFalse(va_c38));
          ghost var va_b56, va_s56 := va_lemma_Store(va_b55, va_s39, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s56) == va_get_globals(va_old_s);  // line 1027 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s56));
          va_s38 := va_lemma_empty(va_s56, va_s38);
        }
        va_s35 := va_lemma_empty(va_s38, va_s35);
      }
      else
      {
        ghost var va_b59 := va_get_block(va_get_ifFalse(va_c35));
        ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s36, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s60) == va_get_globals(va_old_s);  // line 1035 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s60));
        va_s35 := va_lemma_empty(va_s60, va_s35);
      }
      va_s18 := va_lemma_empty(va_s35, va_s18);
    }
    else
    {
      ghost var va_b63 := va_get_block(va_get_ifFalse(va_c18));
      ghost var va_b64, va_s64 := va_lemma_Store(va_b63, va_s19, va_s18, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s64) == va_get_globals(va_old_s);  // line 1043 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s64));
      va_s18 := va_lemma_empty(va_s64, va_s18);
    }
    va_s14 := va_lemma_empty(va_s18, va_s14);
  }
  else
  {
    ghost var va_b67 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b68, va_s68 := va_lemma_Store(va_b67, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s68) == va_get_globals(va_old_s);  // line 1051 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s68));
    va_s14 := va_lemma_empty(va_s68, va_s14);
  }
  ghost var va_b71, va_s71 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b72, va_s72 := va_lemma_POP_OneReg(va_b71, va_s71, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s72, va_sM);
}
//--
//-- WimpDrv_Read_eEHCI_IntrEnable

function method{:opaque} va_code_WimpDrv_Read_eEHCI_IntrEnable():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_eehci_check_slot_id(va_op_reg_reg(ECX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_op_word_reg(ECX)), va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(ECX)), va_CCons(va_code_eehci_read_intr_enable(),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EDX)), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 15} va_lemma_WimpDrv_Read_eEHCI_IntrEnable(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Read_eEHCI_IntrEnable(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    val:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES);
    ((((((ret == TRUE ==> wimpdrv_valid_slot_id(wimpdrv_slot)) && (ret == TRUE ==>
    eehci_valid_slot_id(eehci_slot))) && (ret == TRUE ==> wimpdrv_get_pid(va_get_globals(va_s0),
    wimpdrv_slot) in pids_parse_g_wimp_pids(va_get_globals(va_s0)))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot) ==
    eehci_info_get_pid(va_get_globals(va_s0), eehci_slot))) && (ret == TRUE ==>
    eehci_mem_get_intr_enable_reg(va_get_globals(va_s0), eehci_slot) == val)) &&
    global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM))) &&
    state_equal_except_mstate(va_s0, va_sM)
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
  reveal_va_code_WimpDrv_Read_eEHCI_IntrEnable();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_wimpdrv_check_slotid(va_b12, va_s12, va_sM,
    va_op_reg_reg(EBX), va_op_reg_reg(EAX));
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_eehci_check_slot_id(va_b16, va_s15, va_s14,
      va_op_reg_reg(ECX), va_op_reg_reg(EAX));
    ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_s14);
    ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
      va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
    if (va_cond_c18)
    {
      ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
      ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s19, va_s18, va_op_word_reg(EBX));
      ghost var va_b22, va_s22 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b21, va_s21, va_s18);
      ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s18, va_op_word_reg(EDI),
        va_op_word_reg(ESP), 0);
      ghost var va_b24, va_s24 := va_lemma_POP_VOID(va_b23, va_s23, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b25, va_s25 := va_lemma_PUSH_VOID(va_b24, va_s24, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s25, va_s18, va_op_reg_reg(EAX),
        va_op_word_reg(ECX));
      ghost var va_b27, va_s27 := va_lemma_eehci_info_get_pid(va_b26, va_s26, va_s18,
        va_op_reg_reg(EAX));
      ghost var va_b28, va_s28 := va_lemma_Load(va_b27, va_s27, va_s18, va_op_word_reg(ESI),
        va_op_word_reg(ESP), 0);
      ghost var va_b29, va_s29 := va_lemma_POP_VOID(va_b28, va_s28, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b30, va_s30 := va_lemma_PUSH_VOID(va_b29, va_s29, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b31, va_s31 := va_lemma_PUSH(va_b30, va_s30, va_s18, va_op_word_reg(EDI));
      ghost var va_b32, va_s32 := va_lemma_pids_is_existing_wimp_pid(va_b31, va_s31, va_s18);
      ghost var va_b33, va_s33 := va_lemma_Load(va_b32, va_s32, va_s18, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b34, va_s34 := va_lemma_POP_VOID(va_b33, va_s33, va_s18, 2 * ARCH_WORD_BYTES);
      ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b34, va_s34, va_s18);
      ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
        va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s34, va_s35);
      if (va_cond_c35)
      {
        ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
        ghost var va_s38, va_c38, va_b38 := va_lemma_block(va_b37, va_s36, va_s35);
        ghost var va_cond_c38, va_s39:va_state := va_lemma_ifElse(va_get_ifCond(va_c38),
          va_get_ifTrue(va_c38), va_get_ifFalse(va_c38), va_s36, va_s38);
        if (va_cond_c38)
        {
          ghost var va_b40 := va_get_block(va_get_ifTrue(va_c38));
          ghost var va_b41, va_s41 := va_lemma_PUSH(va_b40, va_s39, va_s38, va_op_word_reg(ECX));
          ghost var va_b42, va_s42 := va_lemma_eehci_read_intr_enable(va_b41, va_s41, va_s38);
          ghost var va_b43, va_s43 := va_lemma_Load(va_b42, va_s42, va_s38, va_op_word_reg(EDX),
            va_op_word_reg(ESP), 0);
          ghost var va_b44, va_s44 := va_lemma_POP_VOID(va_b43, va_s43, va_s38, 1 *
            ARCH_WORD_BYTES);
          ghost var va_b45, va_s45 := va_lemma_Store(va_b44, va_s44, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          ghost var va_b46, va_s46 := va_lemma_Store(va_b45, va_s45, va_s38, va_op_word_reg(EBP), 2
            * ARCH_WORD_BYTES, va_op_word_reg(EDX));
          assert va_get_globals(va_s46) == va_get_globals(va_old_s);  // line 1163 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s46));
          va_s38 := va_lemma_empty(va_s46, va_s38);
        }
        else
        {
          ghost var va_b49 := va_get_block(va_get_ifFalse(va_c38));
          ghost var va_b50, va_s50 := va_lemma_Store(va_b49, va_s39, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s50) == va_get_globals(va_old_s);  // line 1170 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s50));
          va_s38 := va_lemma_empty(va_s50, va_s38);
        }
        va_s35 := va_lemma_empty(va_s38, va_s35);
      }
      else
      {
        ghost var va_b53 := va_get_block(va_get_ifFalse(va_c35));
        ghost var va_b54, va_s54 := va_lemma_Store(va_b53, va_s36, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s54) == va_get_globals(va_old_s);  // line 1178 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s54));
        va_s35 := va_lemma_empty(va_s54, va_s35);
      }
      va_s18 := va_lemma_empty(va_s35, va_s18);
    }
    else
    {
      ghost var va_b57 := va_get_block(va_get_ifFalse(va_c18));
      ghost var va_b58, va_s58 := va_lemma_Store(va_b57, va_s19, va_s18, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s58) == va_get_globals(va_old_s);  // line 1186 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s58));
      va_s18 := va_lemma_empty(va_s58, va_s18);
    }
    va_s14 := va_lemma_empty(va_s18, va_s14);
  }
  else
  {
    ghost var va_b61 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b62, va_s62 := va_lemma_Store(va_b61, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s62) == va_get_globals(va_old_s);  // line 1194 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s62));
    va_s14 := va_lemma_empty(va_s62, va_s14);
  }
  ghost var va_b65, va_s65 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b66, va_s66 := va_lemma_POP_OneReg(va_b65, va_s65, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s66, va_sM);
}
//--
//-- WimpDrv_Write_eEHCI_IntrTarget

function method{:opaque} va_code_WimpDrv_Write_eEHCI_IntrTarget():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_eehci_check_slot_id(va_op_reg_reg(ECX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_op_word_reg(ECX)), va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_eehci_write_intr_target(), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 15} va_lemma_WimpDrv_Write_eEHCI_IntrTarget(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Write_eEHCI_IntrTarget(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2
    * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    ((((((ret == TRUE ==> wimpdrv_valid_slot_id(wimpdrv_slot)) && (ret == TRUE ==>
    eehci_valid_slot_id(eehci_slot))) && (ret == TRUE ==> wimpdrv_get_pid(va_get_globals(va_s0),
    wimpdrv_slot) in pids_parse_g_wimp_pids(va_get_globals(va_s0)))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot) ==
    eehci_info_get_pid(va_get_globals(va_s0), eehci_slot))) && (ret == TRUE ==> (var vaddr :=
    AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES +
    G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset; va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_EEHCI_MEM(), vaddr, new_v)))) && (ret != TRUE ==>
    global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM)))) &&
    (ret != TRUE ==> state_equal_except_mstate(va_s0, va_sM))
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
  reveal_va_code_WimpDrv_Write_eEHCI_IntrTarget();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_wimpdrv_check_slotid(va_b12, va_s12, va_sM,
    va_op_reg_reg(EBX), va_op_reg_reg(EAX));
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_eehci_check_slot_id(va_b16, va_s15, va_s14,
      va_op_reg_reg(ECX), va_op_reg_reg(EAX));
    ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_s14);
    ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
      va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
    if (va_cond_c18)
    {
      ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
      ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s19, va_s18, va_op_word_reg(EBX));
      ghost var va_b22, va_s22 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b21, va_s21, va_s18);
      ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s18, va_op_word_reg(EDI),
        va_op_word_reg(ESP), 0);
      ghost var va_b24, va_s24 := va_lemma_POP_VOID(va_b23, va_s23, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b25, va_s25 := va_lemma_PUSH_VOID(va_b24, va_s24, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s25, va_s18, va_op_reg_reg(EAX),
        va_op_word_reg(ECX));
      ghost var va_b27, va_s27 := va_lemma_eehci_info_get_pid(va_b26, va_s26, va_s18,
        va_op_reg_reg(EAX));
      ghost var va_b28, va_s28 := va_lemma_Load(va_b27, va_s27, va_s18, va_op_word_reg(ESI),
        va_op_word_reg(ESP), 0);
      ghost var va_b29, va_s29 := va_lemma_POP_VOID(va_b28, va_s28, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b30, va_s30 := va_lemma_PUSH_VOID(va_b29, va_s29, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b31, va_s31 := va_lemma_PUSH(va_b30, va_s30, va_s18, va_op_word_reg(EDI));
      ghost var va_b32, va_s32 := va_lemma_pids_is_existing_wimp_pid(va_b31, va_s31, va_s18);
      ghost var va_b33, va_s33 := va_lemma_Load(va_b32, va_s32, va_s18, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b34, va_s34 := va_lemma_POP_VOID(va_b33, va_s33, va_s18, 2 * ARCH_WORD_BYTES);
      ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b34, va_s34, va_s18);
      ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
        va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s34, va_s35);
      if (va_cond_c35)
      {
        ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
        ghost var va_s38, va_c38, va_b38 := va_lemma_block(va_b37, va_s36, va_s35);
        ghost var va_cond_c38, va_s39:va_state := va_lemma_ifElse(va_get_ifCond(va_c38),
          va_get_ifTrue(va_c38), va_get_ifFalse(va_c38), va_s36, va_s38);
        if (va_cond_c38)
        {
          ghost var va_b40 := va_get_block(va_get_ifTrue(va_c38));
          ghost var va_b41, va_s41 := va_lemma_Load(va_b40, va_s39, va_s38, va_op_word_reg(EDX),
            va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
          ghost var va_b42, va_s42 := va_lemma_PUSH(va_b41, va_s41, va_s38, va_op_word_reg(EDX));
          ghost var va_b43, va_s43 := va_lemma_PUSH(va_b42, va_s42, va_s38, va_op_word_reg(ECX));
          ghost var va_b44, va_s44 := va_lemma_eehci_write_intr_target(va_b43, va_s43, va_s38);
          ghost var va_b45, va_s45 := va_lemma_POP_VOID(va_b44, va_s44, va_s38, 2 *
            ARCH_WORD_BYTES);
          ghost var va_b46, va_s46 := va_lemma_Store(va_b45, va_s45, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          va_s38 := va_lemma_empty(va_s46, va_s38);
        }
        else
        {
          ghost var va_b47 := va_get_block(va_get_ifFalse(va_c38));
          ghost var va_b48, va_s48 := va_lemma_Store(va_b47, va_s39, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s48) == va_get_globals(va_old_s);  // line 1317 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s48));
          va_s38 := va_lemma_empty(va_s48, va_s38);
        }
        va_s35 := va_lemma_empty(va_s38, va_s35);
      }
      else
      {
        ghost var va_b51 := va_get_block(va_get_ifFalse(va_c35));
        ghost var va_b52, va_s52 := va_lemma_Store(va_b51, va_s36, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s52) == va_get_globals(va_old_s);  // line 1325 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s52));
        va_s35 := va_lemma_empty(va_s52, va_s35);
      }
      va_s18 := va_lemma_empty(va_s35, va_s18);
    }
    else
    {
      ghost var va_b55 := va_get_block(va_get_ifFalse(va_c18));
      ghost var va_b56, va_s56 := va_lemma_Store(va_b55, va_s19, va_s18, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s56) == va_get_globals(va_old_s);  // line 1333 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s56));
      va_s18 := va_lemma_empty(va_s56, va_s18);
    }
    va_s14 := va_lemma_empty(va_s18, va_s14);
  }
  else
  {
    ghost var va_b59 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s60) == va_get_globals(va_old_s);  // line 1341 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s60));
    va_s14 := va_lemma_empty(va_s60, va_s14);
  }
  ghost var va_b63, va_s63 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b64, va_s64 := va_lemma_POP_OneReg(va_b63, va_s63, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s64, va_sM);
}
//--
//-- WimpDrv_Read_eEHCI_IntrTarget

function method{:opaque} va_code_WimpDrv_Read_eEHCI_IntrTarget():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_eehci_check_slot_id(va_op_reg_reg(ECX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_op_word_reg(ECX)), va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(ECX)), va_CCons(va_code_eehci_read_intr_target(),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EDX)), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 15} va_lemma_WimpDrv_Read_eEHCI_IntrTarget(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Read_eEHCI_IntrTarget(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    val:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES);
    ((((((ret == TRUE ==> wimpdrv_valid_slot_id(wimpdrv_slot)) && (ret == TRUE ==>
    eehci_valid_slot_id(eehci_slot))) && (ret == TRUE ==> wimpdrv_get_pid(va_get_globals(va_s0),
    wimpdrv_slot) in pids_parse_g_wimp_pids(va_get_globals(va_s0)))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot) ==
    eehci_info_get_pid(va_get_globals(va_s0), eehci_slot))) && (ret == TRUE ==>
    eehci_mem_get_intr_target_reg(va_get_globals(va_s0), eehci_slot) == val)) &&
    global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM))) &&
    state_equal_except_mstate(va_s0, va_sM)
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
  reveal_va_code_WimpDrv_Read_eEHCI_IntrTarget();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_wimpdrv_check_slotid(va_b12, va_s12, va_sM,
    va_op_reg_reg(EBX), va_op_reg_reg(EAX));
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_eehci_check_slot_id(va_b16, va_s15, va_s14,
      va_op_reg_reg(ECX), va_op_reg_reg(EAX));
    ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_s14);
    ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
      va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
    if (va_cond_c18)
    {
      ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
      ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s19, va_s18, va_op_word_reg(EBX));
      ghost var va_b22, va_s22 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b21, va_s21, va_s18);
      ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s18, va_op_word_reg(EDI),
        va_op_word_reg(ESP), 0);
      ghost var va_b24, va_s24 := va_lemma_POP_VOID(va_b23, va_s23, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b25, va_s25 := va_lemma_PUSH_VOID(va_b24, va_s24, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s25, va_s18, va_op_reg_reg(EAX),
        va_op_word_reg(ECX));
      ghost var va_b27, va_s27 := va_lemma_eehci_info_get_pid(va_b26, va_s26, va_s18,
        va_op_reg_reg(EAX));
      ghost var va_b28, va_s28 := va_lemma_Load(va_b27, va_s27, va_s18, va_op_word_reg(ESI),
        va_op_word_reg(ESP), 0);
      ghost var va_b29, va_s29 := va_lemma_POP_VOID(va_b28, va_s28, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b30, va_s30 := va_lemma_PUSH_VOID(va_b29, va_s29, va_s18, 1 * ARCH_WORD_BYTES);
      ghost var va_b31, va_s31 := va_lemma_PUSH(va_b30, va_s30, va_s18, va_op_word_reg(EDI));
      ghost var va_b32, va_s32 := va_lemma_pids_is_existing_wimp_pid(va_b31, va_s31, va_s18);
      ghost var va_b33, va_s33 := va_lemma_Load(va_b32, va_s32, va_s18, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b34, va_s34 := va_lemma_POP_VOID(va_b33, va_s33, va_s18, 2 * ARCH_WORD_BYTES);
      ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b34, va_s34, va_s18);
      ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
        va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s34, va_s35);
      if (va_cond_c35)
      {
        ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
        ghost var va_s38, va_c38, va_b38 := va_lemma_block(va_b37, va_s36, va_s35);
        ghost var va_cond_c38, va_s39:va_state := va_lemma_ifElse(va_get_ifCond(va_c38),
          va_get_ifTrue(va_c38), va_get_ifFalse(va_c38), va_s36, va_s38);
        if (va_cond_c38)
        {
          ghost var va_b40 := va_get_block(va_get_ifTrue(va_c38));
          ghost var va_b41, va_s41 := va_lemma_PUSH(va_b40, va_s39, va_s38, va_op_word_reg(ECX));
          ghost var va_b42, va_s42 := va_lemma_eehci_read_intr_target(va_b41, va_s41, va_s38);
          ghost var va_b43, va_s43 := va_lemma_Load(va_b42, va_s42, va_s38, va_op_word_reg(EDX),
            va_op_word_reg(ESP), 0);
          ghost var va_b44, va_s44 := va_lemma_POP_VOID(va_b43, va_s43, va_s38, 1 *
            ARCH_WORD_BYTES);
          ghost var va_b45, va_s45 := va_lemma_Store(va_b44, va_s44, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          ghost var va_b46, va_s46 := va_lemma_Store(va_b45, va_s45, va_s38, va_op_word_reg(EBP), 2
            * ARCH_WORD_BYTES, va_op_word_reg(EDX));
          assert va_get_globals(va_s46) == va_get_globals(va_old_s);  // line 1453 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s46));
          va_s38 := va_lemma_empty(va_s46, va_s38);
        }
        else
        {
          ghost var va_b49 := va_get_block(va_get_ifFalse(va_c38));
          ghost var va_b50, va_s50 := va_lemma_Store(va_b49, va_s39, va_s38, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s50) == va_get_globals(va_old_s);  // line 1460 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s50));
          va_s38 := va_lemma_empty(va_s50, va_s38);
        }
        va_s35 := va_lemma_empty(va_s38, va_s35);
      }
      else
      {
        ghost var va_b53 := va_get_block(va_get_ifFalse(va_c35));
        ghost var va_b54, va_s54 := va_lemma_Store(va_b53, va_s36, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s54) == va_get_globals(va_old_s);  // line 1468 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s54));
        va_s35 := va_lemma_empty(va_s54, va_s35);
      }
      va_s18 := va_lemma_empty(va_s35, va_s18);
    }
    else
    {
      ghost var va_b57 := va_get_block(va_get_ifFalse(va_c18));
      ghost var va_b58, va_s58 := va_lemma_Store(va_b57, va_s19, va_s18, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s58) == va_get_globals(va_old_s);  // line 1476 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s58));
      va_s18 := va_lemma_empty(va_s58, va_s18);
    }
    va_s14 := va_lemma_empty(va_s18, va_s14);
  }
  else
  {
    ghost var va_b61 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b62, va_s62 := va_lemma_Store(va_b61, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s62) == va_get_globals(va_old_s);  // line 1484 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s62));
    va_s14 := va_lemma_empty(va_s62, va_s14);
  }
  ghost var va_b65, va_s65 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b66, va_s66 := va_lemma_POP_OneReg(va_b65, va_s65, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s66, va_sM);
}
//--
//-- WimpDrv_Write_eEHCI_USBTDReg_Impl

function method{:opaque} va_code_WimpDrv_Write_eEHCI_USBTDReg_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_eehci_check_slot_id(va_op_reg_reg(ECX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_eehci_check_usbtd_reg_id(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX), va_op_word_reg(ECX)),
    va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code__WimpDrv_Write_eEHCI_USBTDReg_check_new_value(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_Load(va_op_word_reg(EDX),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDX)),
    va_CCons(va_code_PUSH(va_op_word_reg(ECX)), va_CCons(va_code_eehci_write_usbtd_slot(),
    va_CCons(va_code_POP_VOID(3 * ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(TRUE)), va_CNil()))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))))))))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 70} va_lemma_WimpDrv_Write_eEHCI_USBTDReg_Impl(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Write_eEHCI_USBTDReg_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 20 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 4 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var usbtd_reg_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var new_v:word := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM),
    va_get_reg(ESP, va_s0)); (((((((((ret == TRUE ==> wimpdrv_valid_slot_id(wimpdrv_slot)) && (ret
    == TRUE ==> eehci_valid_slot_id(eehci_slot))) && (ret == TRUE ==> 0 <= usbtd_reg_id <
    eEHCI_USBTD_SlotID_NUMS)) && (ret == TRUE ==> wimpdrv_get_pid(va_get_globals(va_s0),
    wimpdrv_slot) in pids_parse_g_wimp_pids(va_get_globals(va_s0)))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot) ==
    eehci_info_get_pid(va_get_globals(va_s0), eehci_slot))) && (ret == TRUE ==> new_v ==
    USBTD_SlotID_INVALID || usbtd_map_valid_slot_id(new_v))) && (ret == TRUE &&
    usbtd_map_valid_slot_id(new_v) ==> eehci_info_get_pid(va_get_globals(va_s0), eehci_slot) ==
    usbtd_map_get_pid(va_get_globals(va_s0), new_v))) && (ret == TRUE ==> (var vaddr :=
    AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES +
    G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES; va_get_globals(va_sM)
    == global_write_word(va_get_globals(va_s0), G_EEHCI_MEM(), vaddr, new_v)))) && (ret != TRUE ==>
    global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM)))) &&
    (ret != TRUE ==> state_equal_except_mstate(va_s0, va_sM))
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
  reveal_va_code_WimpDrv_Write_eEHCI_USBTDReg_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_wimpdrv_check_slotid(va_b12, va_s12, va_sM,
    va_op_reg_reg(EBX), va_op_reg_reg(EAX));
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_eehci_check_slot_id(va_b16, va_s15, va_s14,
      va_op_reg_reg(ECX), va_op_reg_reg(EAX));
    ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_s14);
    ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
      va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
    if (va_cond_c18)
    {
      ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
      ghost var va_b21, va_s21 := va_lemma_Load(va_b20, va_s19, va_s18, va_op_word_reg(EBX),
        va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
      ghost var va_b22, va_s22 := va_lemma_eehci_check_usbtd_reg_id(va_b21, va_s21, va_s18,
        va_op_reg_reg(EBX), va_op_reg_reg(EAX));
      ghost var va_s23, va_c23, va_b23 := va_lemma_block(va_b22, va_s22, va_s18);
      ghost var va_cond_c23, va_s24:va_state := va_lemma_ifElse(va_get_ifCond(va_c23),
        va_get_ifTrue(va_c23), va_get_ifFalse(va_c23), va_s22, va_s23);
      if (va_cond_c23)
      {
        ghost var va_b25 := va_get_block(va_get_ifTrue(va_c23));
        ghost var va_b26, va_s26 := va_lemma_Load(va_b25, va_s24, va_s23, va_op_word_reg(EBX),
          va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
        ghost var va_b27, va_s27 := va_lemma_PUSH(va_b26, va_s26, va_s23, va_op_word_reg(EBX));
        ghost var va_b28, va_s28 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b27, va_s27, va_s23);
        ghost var va_b29, va_s29 := va_lemma_Load(va_b28, va_s28, va_s23, va_op_word_reg(EDI),
          va_op_word_reg(ESP), 0);
        ghost var va_b30, va_s30 := va_lemma_POP_VOID(va_b29, va_s29, va_s23, 1 * ARCH_WORD_BYTES);
        ghost var va_b31, va_s31 := va_lemma_PUSH_VOID(va_b30, va_s30, va_s23, 1 * ARCH_WORD_BYTES);
        ghost var va_b32, va_s32 := va_lemma_MOV_ToReg(va_b31, va_s31, va_s23, va_op_reg_reg(EAX),
          va_op_word_reg(ECX));
        ghost var va_b33, va_s33 := va_lemma_eehci_info_get_pid(va_b32, va_s32, va_s23,
          va_op_reg_reg(EAX));
        ghost var va_b34, va_s34 := va_lemma_Load(va_b33, va_s33, va_s23, va_op_word_reg(ESI),
          va_op_word_reg(ESP), 0);
        ghost var va_b35, va_s35 := va_lemma_POP_VOID(va_b34, va_s34, va_s23, 1 * ARCH_WORD_BYTES);
        ghost var va_b36, va_s36 := va_lemma_PUSH_VOID(va_b35, va_s35, va_s23, 1 * ARCH_WORD_BYTES);
        ghost var va_b37, va_s37 := va_lemma_PUSH(va_b36, va_s36, va_s23, va_op_word_reg(EDI));
        ghost var va_b38, va_s38 := va_lemma_pids_is_existing_wimp_pid(va_b37, va_s37, va_s23);
        ghost var va_b39, va_s39 := va_lemma_Load(va_b38, va_s38, va_s23, va_op_word_reg(EAX),
          va_op_word_reg(ESP), 0);
        ghost var va_b40, va_s40 := va_lemma_POP_VOID(va_b39, va_s39, va_s23, 2 * ARCH_WORD_BYTES);
        ghost var va_s41, va_c41, va_b41 := va_lemma_block(va_b40, va_s40, va_s23);
        ghost var va_cond_c41, va_s42:va_state := va_lemma_ifElse(va_get_ifCond(va_c41),
          va_get_ifTrue(va_c41), va_get_ifFalse(va_c41), va_s40, va_s41);
        if (va_cond_c41)
        {
          ghost var va_b43 := va_get_block(va_get_ifTrue(va_c41));
          ghost var va_s44, va_c44, va_b44 := va_lemma_block(va_b43, va_s42, va_s41);
          ghost var va_cond_c44, va_s45:va_state := va_lemma_ifElse(va_get_ifCond(va_c44),
            va_get_ifTrue(va_c44), va_get_ifFalse(va_c44), va_s42, va_s44);
          if (va_cond_c44)
          {
            ghost var va_b46 := va_get_block(va_get_ifTrue(va_c44));
            ghost var va_b47, va_s47 := va_lemma_Load(va_b46, va_s45, va_s44, va_op_word_reg(EDX),
              va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
            ghost var va_b48, va_s48 := va_lemma_PUSH(va_b47, va_s47, va_s44, va_op_word_reg(EDX));
            ghost var in_new_v := va_get_reg(EDX, va_s48);
            ghost var va_b50, va_s50 := va_lemma_PUSH(va_b48, va_s48, va_s44, va_op_word_reg(ECX));
            ghost var va_b51, va_s51 :=
              va_lemma__WimpDrv_Write_eEHCI_USBTDReg_check_new_value(va_b50, va_s50, va_s44);
            ghost var va_b52, va_s52 := va_lemma_Load(va_b51, va_s51, va_s44, va_op_word_reg(EAX),
              va_op_word_reg(ESP), 0);
            ghost var va_b53, va_s53 := va_lemma_POP_VOID(va_b52, va_s52, va_s44, 2 *
              ARCH_WORD_BYTES);
            ghost var va_s54, va_c54, va_b54 := va_lemma_block(va_b53, va_s53, va_s44);
            ghost var va_cond_c54, va_s55:va_state := va_lemma_ifElse(va_get_ifCond(va_c54),
              va_get_ifTrue(va_c54), va_get_ifFalse(va_c54), va_s53, va_s54);
            if (va_cond_c54)
            {
              ghost var va_b56 := va_get_block(va_get_ifTrue(va_c54));
              assert usbtd_map_valid_slot_id(in_new_v) ==>
                eehci_info_get_pid(va_get_globals(va_s55), va_get_reg(ECX, va_s55)) ==
                usbtd_map_get_pid(va_get_globals(va_s55), in_new_v);  // line 1617 column 29 of file .\dev/usb2/eehci_ops_impl.vad
              ghost var va_b58, va_s58 := va_lemma_Load(va_b56, va_s55, va_s54,
                va_op_word_reg(EDX), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
              ghost var va_b59, va_s59 := va_lemma_PUSH(va_b58, va_s58, va_s54,
                va_op_word_reg(EDX));
              ghost var va_b60, va_s60 := va_lemma_Load(va_b59, va_s59, va_s54,
                va_op_word_reg(EDX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
              ghost var va_b61, va_s61 := va_lemma_PUSH(va_b60, va_s60, va_s54,
                va_op_word_reg(EDX));
              ghost var va_b62, va_s62 := va_lemma_PUSH(va_b61, va_s61, va_s54,
                va_op_word_reg(ECX));
              ghost var va_b63, va_s63 := va_lemma_eehci_write_usbtd_slot(va_b62, va_s62, va_s54);
              ghost var va_b64, va_s64 := va_lemma_POP_VOID(va_b63, va_s63, va_s54, 3 *
                ARCH_WORD_BYTES);
              ghost var va_b65, va_s65 := va_lemma_Store(va_b64, va_s64, va_s54,
                va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE));
              va_s54 := va_lemma_empty(va_s65, va_s54);
            }
            else
            {
              ghost var va_b66 := va_get_block(va_get_ifFalse(va_c54));
              ghost var va_b67, va_s67 := va_lemma_Store(va_b66, va_s55, va_s54,
                va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE));
              assert va_get_globals(va_s67) == va_get_globals(va_old_s);  // line 1636 column 29 of file .\dev/usb2/eehci_ops_impl.vad
              Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
                va_get_globals(va_s67));
              va_s54 := va_lemma_empty(va_s67, va_s54);
            }
            va_s44 := va_lemma_empty(va_s54, va_s44);
          }
          else
          {
            ghost var va_b70 := va_get_block(va_get_ifFalse(va_c44));
            ghost var va_b71, va_s71 := va_lemma_Store(va_b70, va_s45, va_s44, va_op_word_reg(EBP),
              ARCH_WORD_BYTES, va_const_word(FALSE));
            assert va_get_globals(va_s71) == va_get_globals(va_old_s);  // line 1644 column 25 of file .\dev/usb2/eehci_ops_impl.vad
            Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
              va_get_globals(va_s71));
            va_s44 := va_lemma_empty(va_s71, va_s44);
          }
          va_s41 := va_lemma_empty(va_s44, va_s41);
        }
        else
        {
          ghost var va_b74 := va_get_block(va_get_ifFalse(va_c41));
          ghost var va_b75, va_s75 := va_lemma_Store(va_b74, va_s42, va_s41, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s75) == va_get_globals(va_old_s);  // line 1652 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s75));
          va_s41 := va_lemma_empty(va_s75, va_s41);
        }
        va_s23 := va_lemma_empty(va_s41, va_s23);
      }
      else
      {
        ghost var va_b78 := va_get_block(va_get_ifFalse(va_c23));
        ghost var va_b79, va_s79 := va_lemma_Store(va_b78, va_s24, va_s23, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s79) == va_get_globals(va_old_s);  // line 1660 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s79));
        va_s23 := va_lemma_empty(va_s79, va_s23);
      }
      va_s18 := va_lemma_empty(va_s23, va_s18);
    }
    else
    {
      ghost var va_b82 := va_get_block(va_get_ifFalse(va_c18));
      ghost var va_b83, va_s83 := va_lemma_Store(va_b82, va_s19, va_s18, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s83) == va_get_globals(va_old_s);  // line 1668 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s83));
      va_s18 := va_lemma_empty(va_s83, va_s18);
    }
    va_s14 := va_lemma_empty(va_s18, va_s14);
  }
  else
  {
    ghost var va_b86 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b87, va_s87 := va_lemma_Store(va_b86, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s87) == va_get_globals(va_old_s);  // line 1676 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s87));
    va_s14 := va_lemma_empty(va_s87, va_s14);
  }
  ghost var va_b90, va_s90 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b91, va_s91 := va_lemma_POP_OneReg(va_b90, va_s90, va_sM, va_op_reg_reg(EBP));
  Lemma_modify_regs_stateeq(va_old_s, va_s91);
  va_sM := va_lemma_empty(va_s91, va_sM);
}
//--
//-- WimpDrv_Read_eEHCI_USBTDReg_Impl

function method{:opaque} va_code_WimpDrv_Read_eEHCI_USBTDReg_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_eehci_check_slot_id(va_op_reg_reg(ECX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_eehci_check_usbtd_reg_id(va_op_reg_reg(EDX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_op_word_reg(ECX)), va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_eehci_read_usbtd_slot(), va_CCons(va_code_Load(va_op_word_reg(EDX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES, va_op_word_reg(EDX)),
    va_CNil()))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 15} va_lemma_WimpDrv_Read_eEHCI_USBTDReg_Impl(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Read_eEHCI_USBTDReg_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var usbtd_reg_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP,
    va_s0)); var val:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); (((((((ret == TRUE ==> wimpdrv_valid_slot_id(wimpdrv_slot)) && (ret == TRUE
    ==> eehci_valid_slot_id(eehci_slot))) && (ret == TRUE ==> 0 <= usbtd_reg_id <
    eEHCI_USBTD_SlotID_NUMS)) && (ret == TRUE ==> wimpdrv_get_pid(va_get_globals(va_s0),
    wimpdrv_slot) in pids_parse_g_wimp_pids(va_get_globals(va_s0)))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot) ==
    eehci_info_get_pid(va_get_globals(va_s0), eehci_slot))) && (ret == TRUE ==>
    eehci_mem_get_usbtd_reg(va_get_globals(va_s0), eehci_slot, usbtd_reg_id) == val)) &&
    global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM))) &&
    state_equal_except_mstate(va_s0, va_sM)
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
  reveal_va_code_WimpDrv_Read_eEHCI_USBTDReg_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_wimpdrv_check_slotid(va_b12, va_s12, va_sM,
    va_op_reg_reg(EBX), va_op_reg_reg(EAX));
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_eehci_check_slot_id(va_b16, va_s15, va_s14,
      va_op_reg_reg(ECX), va_op_reg_reg(EAX));
    ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_s14);
    ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
      va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
    if (va_cond_c18)
    {
      ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
      ghost var va_b21, va_s21 := va_lemma_Load(va_b20, va_s19, va_s18, va_op_word_reg(EDX),
        va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
      ghost var va_b22, va_s22 := va_lemma_eehci_check_usbtd_reg_id(va_b21, va_s21, va_s18,
        va_op_reg_reg(EDX), va_op_reg_reg(EAX));
      ghost var va_s23, va_c23, va_b23 := va_lemma_block(va_b22, va_s22, va_s18);
      ghost var va_cond_c23, va_s24:va_state := va_lemma_ifElse(va_get_ifCond(va_c23),
        va_get_ifTrue(va_c23), va_get_ifFalse(va_c23), va_s22, va_s23);
      if (va_cond_c23)
      {
        ghost var va_b25 := va_get_block(va_get_ifTrue(va_c23));
        ghost var va_b26, va_s26 := va_lemma_PUSH(va_b25, va_s24, va_s23, va_op_word_reg(EBX));
        ghost var va_b27, va_s27 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b26, va_s26, va_s23);
        ghost var va_b28, va_s28 := va_lemma_Load(va_b27, va_s27, va_s23, va_op_word_reg(EDI),
          va_op_word_reg(ESP), 0);
        ghost var va_b29, va_s29 := va_lemma_POP_VOID(va_b28, va_s28, va_s23, 1 * ARCH_WORD_BYTES);
        ghost var va_b30, va_s30 := va_lemma_PUSH_VOID(va_b29, va_s29, va_s23, 1 * ARCH_WORD_BYTES);
        ghost var va_b31, va_s31 := va_lemma_MOV_ToReg(va_b30, va_s30, va_s23, va_op_reg_reg(EAX),
          va_op_word_reg(ECX));
        ghost var va_b32, va_s32 := va_lemma_eehci_info_get_pid(va_b31, va_s31, va_s23,
          va_op_reg_reg(EAX));
        ghost var va_b33, va_s33 := va_lemma_Load(va_b32, va_s32, va_s23, va_op_word_reg(ESI),
          va_op_word_reg(ESP), 0);
        ghost var va_b34, va_s34 := va_lemma_POP_VOID(va_b33, va_s33, va_s23, 1 * ARCH_WORD_BYTES);
        ghost var va_b35, va_s35 := va_lemma_PUSH_VOID(va_b34, va_s34, va_s23, 1 * ARCH_WORD_BYTES);
        ghost var va_b36, va_s36 := va_lemma_PUSH(va_b35, va_s35, va_s23, va_op_word_reg(EDI));
        ghost var va_b37, va_s37 := va_lemma_pids_is_existing_wimp_pid(va_b36, va_s36, va_s23);
        ghost var va_b38, va_s38 := va_lemma_Load(va_b37, va_s37, va_s23, va_op_word_reg(EAX),
          va_op_word_reg(ESP), 0);
        ghost var va_b39, va_s39 := va_lemma_POP_VOID(va_b38, va_s38, va_s23, 2 * ARCH_WORD_BYTES);
        ghost var va_s40, va_c40, va_b40 := va_lemma_block(va_b39, va_s39, va_s23);
        ghost var va_cond_c40, va_s41:va_state := va_lemma_ifElse(va_get_ifCond(va_c40),
          va_get_ifTrue(va_c40), va_get_ifFalse(va_c40), va_s39, va_s40);
        if (va_cond_c40)
        {
          ghost var va_b42 := va_get_block(va_get_ifTrue(va_c40));
          ghost var va_s43, va_c43, va_b43 := va_lemma_block(va_b42, va_s41, va_s40);
          ghost var va_cond_c43, va_s44:va_state := va_lemma_ifElse(va_get_ifCond(va_c43),
            va_get_ifTrue(va_c43), va_get_ifFalse(va_c43), va_s41, va_s43);
          if (va_cond_c43)
          {
            ghost var va_b45 := va_get_block(va_get_ifTrue(va_c43));
            ghost var va_b46, va_s46 := va_lemma_Load(va_b45, va_s44, va_s43, va_op_word_reg(EDX),
              va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
            ghost var va_b47, va_s47 := va_lemma_PUSH(va_b46, va_s46, va_s43, va_op_word_reg(EDX));
            ghost var va_b48, va_s48 := va_lemma_PUSH(va_b47, va_s47, va_s43, va_op_word_reg(ECX));
            ghost var va_b49, va_s49 := va_lemma_eehci_read_usbtd_slot(va_b48, va_s48, va_s43);
            ghost var va_b50, va_s50 := va_lemma_Load(va_b49, va_s49, va_s43, va_op_word_reg(EDX),
              va_op_word_reg(ESP), 0);
            ghost var va_b51, va_s51 := va_lemma_POP_VOID(va_b50, va_s50, va_s43, 2 *
              ARCH_WORD_BYTES);
            ghost var va_b52, va_s52 := va_lemma_Store(va_b51, va_s51, va_s43, va_op_word_reg(EBP),
              ARCH_WORD_BYTES, va_const_word(TRUE));
            ghost var va_b53, va_s53 := va_lemma_Store(va_b52, va_s52, va_s43, va_op_word_reg(EBP),
              2 * ARCH_WORD_BYTES, va_op_word_reg(EDX));
            assert va_get_globals(va_s53) == va_get_globals(va_old_s);  // line 1799 column 25 of file .\dev/usb2/eehci_ops_impl.vad
            Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
              va_get_globals(va_s53));
            va_s43 := va_lemma_empty(va_s53, va_s43);
          }
          else
          {
            ghost var va_b56 := va_get_block(va_get_ifFalse(va_c43));
            ghost var va_b57, va_s57 := va_lemma_Store(va_b56, va_s44, va_s43, va_op_word_reg(EBP),
              ARCH_WORD_BYTES, va_const_word(FALSE));
            assert va_get_globals(va_s57) == va_get_globals(va_old_s);  // line 1806 column 25 of file .\dev/usb2/eehci_ops_impl.vad
            Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
              va_get_globals(va_s57));
            va_s43 := va_lemma_empty(va_s57, va_s43);
          }
          va_s40 := va_lemma_empty(va_s43, va_s40);
        }
        else
        {
          ghost var va_b60 := va_get_block(va_get_ifFalse(va_c40));
          ghost var va_b61, va_s61 := va_lemma_Store(va_b60, va_s41, va_s40, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s61) == va_get_globals(va_old_s);  // line 1814 column 21 of file .\dev/usb2/eehci_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s61));
          va_s40 := va_lemma_empty(va_s61, va_s40);
        }
        va_s23 := va_lemma_empty(va_s40, va_s23);
      }
      else
      {
        ghost var va_b64 := va_get_block(va_get_ifFalse(va_c23));
        ghost var va_b65, va_s65 := va_lemma_Store(va_b64, va_s24, va_s23, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s65) == va_get_globals(va_old_s);  // line 1822 column 17 of file .\dev/usb2/eehci_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s65));
        va_s23 := va_lemma_empty(va_s65, va_s23);
      }
      va_s18 := va_lemma_empty(va_s23, va_s18);
    }
    else
    {
      ghost var va_b68 := va_get_block(va_get_ifFalse(va_c18));
      ghost var va_b69, va_s69 := va_lemma_Store(va_b68, va_s19, va_s18, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s69) == va_get_globals(va_old_s);  // line 1830 column 13 of file .\dev/usb2/eehci_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s69));
      va_s18 := va_lemma_empty(va_s69, va_s18);
    }
    va_s14 := va_lemma_empty(va_s18, va_s14);
  }
  else
  {
    ghost var va_b72 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b73, va_s73 := va_lemma_Store(va_b72, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s73) == va_get_globals(va_old_s);  // line 1838 column 9 of file .\dev/usb2/eehci_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s73));
    va_s14 := va_lemma_empty(va_s73, va_s14);
  }
  ghost var va_b76, va_s76 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b77, va_s77 := va_lemma_POP_OneReg(va_b76, va_s76, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s77, va_sM);
}
//--
predicate eechi_activate_globalvars_relation(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:word, eehci_id:word, eehci_handle:word, new_pid:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires eehci_valid_slot_id(eehci_slot)
{
    // Only <g_eehci_mem> and <g_eehci_info> is changed
    globals_other_gvar_unchanged_2vars(old_globals, new_globals, G_EEHCI_MEM(), G_EEHCIs_Info()) &&

    // Other slots in <g_eehci_mem> and <g_eehci_info> is unchanged
    (forall i :: eehci_valid_slot_id(i) && i != eehci_slot
        ==> (p_eehci_mem_equal(old_globals, new_globals, i) && eechi_info_equal(old_globals, new_globals, i))
    ) &&

    // The info of eEHCI slot in <g_eehci_info> is modified correctly
    eehci_info_get_reserved(new_globals, eehci_slot) == 0 &&
    eehci_info_get_pid(new_globals, eehci_slot) == WS_PartitionID(new_pid) &&

    // The eEHCI slot in <g_eehci_mem> is modified correctly
    eehci_mem_get_eehci_id(new_globals, eehci_slot) == eehci_id &&
    eehci_mem_get_handle_reg(new_globals, eehci_slot) == eehci_handle &&
    eehci_mem_get_config_reg(new_globals, eehci_slot) == eEHCI_Config_Disable &&
    eehci_mem_get_status_reg(new_globals, eehci_slot) == 0 &&
    eehci_mem_get_intr_enable_reg(new_globals, eehci_slot) == eEHCI_Intr_Disable &&
    eehci_mem_get_intr_target_reg(new_globals, eehci_slot) == 0 &&
    (forall i :: 0 <= i < eEHCI_USBTD_SlotID_NUMS ==> eehci_mem_get_usbtd_reg(new_globals, eehci_slot, i) == USBTD_SlotID_INVALID) &&

    (true)
}

predicate eechi_deactivate_globalvars_relation(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires eehci_valid_slot_id(eehci_slot)
{
    // Only <g_eehci_mem> and <g_eehci_info> is changed
    globals_other_gvar_unchanged_2vars(old_globals, new_globals, G_EEHCI_MEM(), G_EEHCIs_Info()) &&

    // Other slots in <g_eehci_mem> and <g_eehci_info> is unchanged
    (forall i :: eehci_valid_slot_id(i) && i != eehci_slot
        ==> (p_eehci_mem_equal(old_globals, new_globals, i) && eechi_info_equal(old_globals, new_globals, i))
    ) &&

    // The info of eEHCI slot in <g_eehci_info> is modified correctly
    eehci_info_get_reserved(new_globals, eehci_slot) == 0 &&
    eehci_info_get_pid(new_globals, eehci_slot) == WS_PartitionID(PID_INVALID) &&

    // The eEHCI slot in <g_eehci_mem> is modified correctly
    eehci_mem_get_eehci_id(new_globals, eehci_slot) == eEHCI_ID_INVALID &&
    eehci_mem_get_handle_reg(new_globals, eehci_slot) == eehci_mem_get_handle_reg(old_globals, eehci_slot) &&
    eehci_mem_get_config_reg(new_globals, eehci_slot) == eehci_mem_get_config_reg(old_globals, eehci_slot) &&
    eehci_mem_get_status_reg(new_globals, eehci_slot) == eehci_mem_get_status_reg(old_globals, eehci_slot) &&
    eehci_mem_get_intr_enable_reg(new_globals, eehci_slot) == eehci_mem_get_intr_enable_reg(old_globals, eehci_slot) &&
    eehci_mem_get_intr_target_reg(new_globals, eehci_slot) == eehci_mem_get_intr_target_reg(old_globals, eehci_slot) &&
    (forall i :: 0 <= i < eEHCI_USBTD_SlotID_NUMS ==> p_eehci_mem_usbtd_regs_equal(old_globals, new_globals, i)) &&

    (true)
}

// Prove the property 2 of <EEHCI_Activate>
lemma Lemma_EEHCI_Activate_ProveProperty2(
    old_globals:globalsmap, globals1:globalsmap, new_globals:globalsmap, slot:word, new_eehci_id:word, new_handle:word, new_pid:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires eehci_valid_slot_id(slot)

    requires var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
             is_gvar_valid_addr(G_EEHCI_MEM(), vaddr1)

    requires ffi_eehci_activate_globals_relationship(old_globals, globals1, slot, new_eehci_id, new_handle, TRUE);
    requires eehci_info_only_change_slot_newvalue(globals1, new_globals, slot, 0, new_pid);

    ensures eechi_activate_globalvars_relation(old_globals, new_globals, slot, new_eehci_id, new_handle, new_pid)
{
    reveal eehci_mem_cleared_all_regs();

    var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset;

    var new_globals1 := global_write_word(old_globals, G_EEHCI_MEM(), vaddr1, new_eehci_id);
    var new_globals2 := global_write_word(new_globals1, G_EEHCI_MEM(), vaddr2, new_handle);
    assert eehci_mem_cleared_all_regs(new_globals2, globals1, slot);
    
    reveal p_eehci_mem_equal();
    reveal p_eehci_mem_usbtd_regs_equal();
    reveal eechi_info_equal();
    forall i | eehci_valid_slot_id(i) && i != slot
        ensures p_eehci_mem_equal(old_globals, new_globals, i)
        ensures eechi_info_equal(old_globals, new_globals, i)
    {
        // Prove p_eehci_mem_equal(old_globals, new_globals, i)
        assert p_eehci_mem_equal(old_globals, new_globals1, i);
        assert p_eehci_mem_equal(new_globals1, new_globals2, i);
        assert p_eehci_mem_equal(new_globals2, globals1, i);

        assert global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());
        assert p_eehci_mem_equal(old_globals, new_globals, i);

        // Prove eechi_info_equal(old_globals, new_globals, i)
        assert eechi_info_equal(old_globals, new_globals, i);
    }
}

// Prove the property 2 of <EEHCI_Deactivate>
lemma Lemma_EEHCI_Deactivate_ProveProperty2(
    old_globals:globalsmap, globals1:globalsmap, new_globals:globalsmap, slot:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires eehci_valid_slot_id(slot)

    requires var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
             is_gvar_valid_addr(G_EEHCI_MEM(), vaddr1)

    requires eehci_info_only_change_slot_newvalue(old_globals, globals1, slot, 0, PID_INVALID);
    requires ffi_eehci_deactivate_globals_relationship(globals1, new_globals, slot);

    ensures eechi_deactivate_globalvars_relation(old_globals, new_globals, slot)
{
    reveal eehci_mem_cleared_all_regs();

    var vaddr1 := AddressOfGlobal(G_EEHCIs_Info()) + slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_Info_ENTRY_Reserved_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_EEHCIs_Info()) + slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_INFO_ENTRY_PID_BytesOffset;

    // Apply eehci_info_only_change_slot_newvalue
    assert eehci_info_only_change_slot_newvalue(old_globals, globals1, slot, 0, PID_INVALID);
    var t_globals1 := global_write_word(old_globals, G_EEHCIs_Info(), vaddr1, 0);
    assert globals1 == global_write_word(t_globals1, G_EEHCIs_Info(), vaddr2, PID_INVALID);
    
    reveal p_eehci_mem_equal();
    reveal p_eehci_mem_usbtd_regs_equal();
    reveal eechi_info_equal();
}
