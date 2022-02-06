include "usb_tds_ops_impl.gen.dfy"
include "usb_tds_checks_qh.gen.dfy"
include "usb_tds_ops.i.dfy"
//-- _usbtd_slot_submit_and_verify_qh32_inner

function method{:opaque} va_code__usbtd_slot_submit_and_verify_qh32_inner():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_CALL_USBTD_Backup(), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 9 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 8 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 7 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 6 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_PUSH(va_const_word(QH32_SIZE_BYTES)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code__usbtd_slot_submit(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0),
    va_CCons(va_code_POP_VOID(10 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_usbtd_verify_qh32(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDI), va_const_word(0)),
    va_CCons(va_code_SetBit(va_op_word_reg(EDI), USBTD_SLOT_FLAG_SubmitDone_Bit),
    va_CCons(va_code_SetBit(va_op_word_reg(EDI), USBTD_SLOT_FLAG_SlotSecure_Bit),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_usbtd_set_flags(), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())))))))))), va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_CALL_USBTD_Restore(), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))))))), va_CNil()))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))))))))))))))))))
}

lemma{:timeLimitMultiplier 200} va_lemma__usbtd_slot_submit_and_verify_qh32_inner(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbtd_slot_submit_and_verify_qh32_inner(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 26 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + FFI_USBTD_Qh32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES
    + 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := 9 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    (usbtd_map_valid_slot_id(td_slot) && eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_s0),
    td_slot)) && usbtds_verifiedtds_do_not_associate_usbtd(va_get_globals(va_s0), td_slot)
  requires var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_slot_valid_pid(va_get_globals(va_s0), td_slot)
  requires var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_get_flags(va_get_globals(va_s0), td_slot) == 0
  requires var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_get_type(va_get_globals(va_s0), td_slot) == USBTDs_TYPE_QH32
  requires var usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 8 *
    ARCH_WORD_BYTES); usbpdev_slot == WimpUSBPDev_SlotID_EMPTY ||
    usbpdev_valid_slot_id(usbpdev_slot)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1
    * ARCH_WORD_BYTES); var usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 8 * ARCH_WORD_BYTES); var input_param1:uint32 := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 5 * ARCH_WORD_BYTES); var input_param2:uint32 :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES); var
    input_param3:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 7 *
    ARCH_WORD_BYTES); var eehci_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)
    + 3 * ARCH_WORD_BYTES); var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); (((ret ==
    TRUE ==> p_usbtd_slot_submit_and_verify_usbtd_ret_global(va_get_globals(va_s0),
    va_get_globals(va_sM), td_slot)) && (ret == TRUE ==> usbtd_map_get_type(va_get_globals(va_sM),
    td_slot) == USBTDs_TYPE_QH32 && usbtd_map_get_flags(va_get_globals(va_sM), td_slot) ==
    SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit))) && (ret ==
    TRUE ==> p_usbtd_slot_submit_modification_to_usbtd(va_get_globals(va_sM), td_slot,
    wimpdrv_slot_id, usbpdev_slot, input_param1, input_param2, input_param3, USBTDs_TYPE_QH32,
    eehci_id))) && (ret != TRUE ==> global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0),
    va_get_globals(va_sM)))
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
  reveal_va_code__usbtd_slot_submit_and_verify_qh32_inner();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var orig_esp := va_get_reg(ESP, va_s7);
  ghost var orig_ebp := va_get_reg(EBP, va_s7);
  assert IsAddrInStack(orig_esp - WK_STACK_FOR_EXTERNEL_FUNCS_SZ);  // line 114 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  ghost var va_b11, va_s11 := va_lemma_Load(va_b7, va_s7, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_PUSH(va_b11, va_s11, va_sM, va_op_word_reg(EDI));
  ghost var in_td_slot := va_get_reg(EDI, va_s12);
  ghost var va_b14, va_s14 := va_lemma_CALL_USBTD_Backup(va_b12, va_s12, va_sM);
  ghost var va_b15, va_s15 := va_lemma_POP_VOID(va_b14, va_s14, va_sM, 1 * ARCH_WORD_BYTES);
  assert va_get_reg(ESP, va_s15) == orig_esp;  // line 122 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  ghost var globals1 := va_get_globals(va_s15);
  Lemma_ffi_usbtd_backup_stack_and_globals_ImpliesNonScratchpadGlobalVarsUnchanged(va_get_globals(va_old_s),
    globals1, in_td_slot);
  assert global_non_scratchpad_vars_are_unchanged(va_get_globals(va_old_s), globals1);  // line 126 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  Lemma_eehci_mem_no_ref_to_usbtd_slot_HoldIfOnlyScratchpadGlobalVarsModified(va_get_globals(va_old_s),
    globals1, in_td_slot);
  assert eehci_mem_no_ref_to_usbtd_slot(globals1, in_td_slot);  // line 128 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  Lemma_ffi_usbtd_backup_stack_and_globals_ImpliesIDOfUSBTDIsWrittenInTempUSBTD(va_get_globals(va_old_s),
    globals1, in_td_slot);
  Lemma_ffi_usbtd_backup_stack_and_globals_ImpliesPIDOfUSBTDIsWrittenInTempUSBTD(va_get_globals(va_old_s),
    globals1, in_td_slot);
  assert usbtd_map_get_pid(va_get_globals(va_old_s), in_td_slot) == usbtd_temp_get_pid(globals1); 
    // line 132 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  Lemma_ffi_usbtd_backup_stack_and_globals_inner_TempUSBTDMustBeValid(va_get_globals(va_old_s),
    globals1, in_td_slot);
  assert usbtd_temp_valid_id(globals1);  // line 135 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert usbtd_temp_valid_pid(globals1);  // line 136 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert usbtd_temp_valid_type(globals1);  // line 137 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert usbtd_temp_valid_busid(globals1);  // line 138 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert usbtd_temp_valid_wimpdrv_slotid(globals1);  // line 139 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert usbtd_temp_valid_usbpdev_slotid(globals1);  // line 140 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  Lemma_ffi_usbtd_backup_stack_and_globals_ProveTempUSBTDFlagsIsEmpty(va_get_globals(va_old_s),
    globals1, in_td_slot);
  assert usbtd_temp_get_flags(globals1) == 0;  // line 143 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  Lemma_ffi_usbtd_backup_stack_and_globals_PreserveUSBTDFlags(va_get_globals(va_old_s), globals1,
    in_td_slot);
  assert usbtd_map_get_flags(globals1, in_td_slot) == 0;  // line 146 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  Lemma_TestBit_ReturnFalseIfANumberIs0();
  Lemma_TestBit_ReturnFalse_IfBitNotSetAndAfterSetOtherBits(USBTD_SLOT_FLAG_SlotSecure_Bit);
  assert TestBit(usbtd_map_get_flags(globals1, in_td_slot), USBTD_SLOT_FLAG_SlotSecure_Bit) ==
    false;  // line 149 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  Lemma_usbtds_verifiedtds_do_not_associate_usbtd_HoldIfNonScratchpadGVarsAreUnmodified(va_get_globals(va_old_s),
    globals1, in_td_slot);
  assert usbtds_verifiedtds_do_not_associate_usbtd(globals1, in_td_slot);  // line 152 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  Lemma_ffi_usbtd_backup_stack_and_globals_PreserveUSBTDType(va_get_globals(va_old_s), globals1,
    in_td_slot);
  assert usbtd_map_get_type(globals1, in_td_slot) == USBTDs_TYPE_QH32;  // line 155 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  ghost var va_b43, va_s43 := va_lemma_Load(va_b15, va_s15, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 9 * ARCH_WORD_BYTES);
  ghost var va_b44, va_s44 := va_lemma_PUSH(va_b43, va_s43, va_sM, va_op_word_reg(EDI));
  ghost var va_b45, va_s45 := va_lemma_Load(va_b44, va_s44, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 8 * ARCH_WORD_BYTES);
  ghost var va_b46, va_s46 := va_lemma_PUSH(va_b45, va_s45, va_sM, va_op_word_reg(EDI));
  ghost var va_b47, va_s47 := va_lemma_Load(va_b46, va_s46, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 7 * ARCH_WORD_BYTES);
  ghost var va_b48, va_s48 := va_lemma_PUSH(va_b47, va_s47, va_sM, va_op_word_reg(EDI));
  ghost var va_b49, va_s49 := va_lemma_Load(va_b48, va_s48, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 6 * ARCH_WORD_BYTES);
  ghost var va_b50, va_s50 := va_lemma_PUSH(va_b49, va_s49, va_sM, va_op_word_reg(EDI));
  ghost var va_b51, va_s51 := va_lemma_PUSH(va_b50, va_s50, va_sM, va_const_word(QH32_SIZE_BYTES));
  assert va_get_reg(EBP, va_s51) == orig_ebp;  // line 167 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert va_get_reg(ESP, va_s51) == orig_esp - 5 * ARCH_WORD_BYTES;  // line 168 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  ghost var va_b54, va_s54 := va_lemma_Load(va_b51, va_s51, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES);
  ghost var va_b55, va_s55 := va_lemma_PUSH(va_b54, va_s54, va_sM, va_op_word_reg(EDI));
  ghost var va_b56, va_s56 := va_lemma_Load(va_b55, va_s55, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
  ghost var va_b57, va_s57 := va_lemma_PUSH(va_b56, va_s56, va_sM, va_op_word_reg(EDI));
  ghost var va_b58, va_s58 := va_lemma_Load(va_b57, va_s57, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var va_b59, va_s59 := va_lemma_PUSH(va_b58, va_s58, va_sM, va_op_word_reg(EDI));
  assert va_get_reg(EBP, va_s59) == orig_ebp;  // line 175 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert va_get_reg(ESP, va_s59) == orig_esp - 8 * ARCH_WORD_BYTES;  // line 176 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  ghost var va_b62, va_s62 := va_lemma_Load(va_b59, va_s59, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b63, va_s63 := va_lemma_PUSH(va_b62, va_s62, va_sM, va_op_word_reg(EDI));
  ghost var va_b64, va_s64 := va_lemma_Load(va_b63, va_s63, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b65, va_s65 := va_lemma_PUSH(va_b64, va_s64, va_sM, va_op_word_reg(EDI));
  assert va_get_reg(EDI, va_s65) == in_td_slot;  // line 181 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  ghost var va_b67, va_s67 := va_lemma__usbtd_slot_submit(va_b65, va_s65, va_sM);
  ghost var globals2 := va_get_globals(va_s67);
  ghost var va_b69, va_s69 := va_lemma_Load(va_b67, va_s67, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0);
  ghost var va_b70, va_s70 := va_lemma_POP_VOID(va_b69, va_s69, va_sM, 10 * ARCH_WORD_BYTES);
  assert va_get_reg(ESP, va_s70) == orig_esp;  // line 186 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert va_get_reg(EBP, va_s70) == orig_ebp;  // line 187 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert usbtd_temp_valid_pid(globals2);  // line 189 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert usbtd_temp_valid_type(globals2);  // line 190 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert usbtd_temp_valid_busid(globals2);  // line 191 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert usbtd_temp_valid_wimpdrv_slotid(globals2);  // line 192 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  assert usbtd_temp_valid_usbpdev_slotid(globals2);  // line 193 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  ghost var va_s78, va_c78, va_b78 := va_lemma_block(va_b70, va_s70, va_sM);
  ghost var va_cond_c78, va_s79:va_state := va_lemma_ifElse(va_get_ifCond(va_c78),
    va_get_ifTrue(va_c78), va_get_ifFalse(va_c78), va_s70, va_s78);
  if (va_cond_c78)
  {
    ghost var va_b80 := va_get_block(va_get_ifTrue(va_c78));
    assert usbtd_map_get_type(globals2, in_td_slot) == USBTDs_TYPE_QH32;  // line 197 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    assert usbtd_temp_get_flags(globals1) == usbtd_temp_get_flags(globals2);  // line 198 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    assert usbtd_temp_get_flags(globals2) == 0;  // line 199 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    assert usbtd_map_get_flags(globals2, in_td_slot) == SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit); 
      // line 200 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    Lemma_TestBit_ReturnFalseIfANumberIs0();
    Lemma_TestBit_ReturnFalse_IfBitNotSetAndAfterSetOtherBits(USBTD_SLOT_FLAG_SlotSecure_Bit);
    assert TestBit(usbtd_map_get_flags(globals2, in_td_slot), USBTD_SLOT_FLAG_SlotSecure_Bit) ==
      false;  // line 203 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    assert p_usbtd_slot_submit_usbtd_ret_global(globals1, globals2, in_td_slot);  // line 205 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    Lemma__usbtd_slot_submit_usbtd_UnmodifiedGEEHCIMem(globals1, globals2, in_td_slot);
    assert global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2,
      G_EEHCI_MEM());  // line 207 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    Lemma_eehci_mem_no_ref_to_usbtd_slot_Equivilant(globals1, globals2, in_td_slot);
    assert eehci_mem_no_ref_to_usbtd_slot(globals2, in_td_slot);  // line 209 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    ghost var va_b93, va_s93 := va_lemma_Load(va_b80, va_s79, va_s78, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
    ghost var va_b94, va_s94 := va_lemma_PUSH(va_b93, va_s93, va_s78, va_op_word_reg(EDI));
    ghost var va_b95, va_s95 := va_lemma_Load(va_b94, va_s94, va_s78, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
    ghost var va_b96, va_s96 := va_lemma_PUSH(va_b95, va_s95, va_s78, va_op_word_reg(EDI));
    ghost var va_b97, va_s97 := va_lemma_usbtd_verify_qh32(va_b96, va_s96, va_s78);
    ghost var va_b98, va_s98 := va_lemma_Load(va_b97, va_s97, va_s78, va_op_word_reg(EDI),
      va_op_word_reg(ESP), 0);
    assert va_get_reg(ESP, va_s98) == orig_esp - 2 * ARCH_WORD_BYTES;  // line 218 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    ghost var va_b100, va_s100 := va_lemma_POP_VOID(va_b98, va_s98, va_s78, 2 * ARCH_WORD_BYTES);
    assert va_get_reg(ESP, va_s100) == orig_esp;  // line 220 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    ghost var globals3 := va_get_globals(va_s100);
    assert globals3 == globals2;  // line 223 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    assert eehci_mem_no_ref_to_usbtd_slot(globals3, in_td_slot);  // line 224 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    Lemma_usbtd_slot_submit_and_verify_qh32_inner_impl_ProveIDUniquenessForTempUSBTD(globals1,
      globals2, globals3, in_td_slot);
    ghost var va_s106, va_c106, va_b106 := va_lemma_block(va_b100, va_s100, va_s78);
    ghost var va_cond_c106, va_s107:va_state := va_lemma_ifElse(va_get_ifCond(va_c106),
      va_get_ifTrue(va_c106), va_get_ifFalse(va_c106), va_s100, va_s106);
    if (va_cond_c106)
    {
      ghost var va_b108 := va_get_block(va_get_ifTrue(va_c106));
      ghost var va_b109, va_s109 := va_lemma_MOV_ToReg(va_b108, va_s107, va_s106,
        va_op_reg_reg(EDI), va_const_word(0));
      ghost var va_b110, va_s110 := va_lemma_SetBit(va_b109, va_s109, va_s106, va_op_word_reg(EDI),
        USBTD_SLOT_FLAG_SubmitDone_Bit);
      ghost var va_b111, va_s111 := va_lemma_SetBit(va_b110, va_s110, va_s106, va_op_word_reg(EDI),
        USBTD_SLOT_FLAG_SlotSecure_Bit);
      ghost var va_b112, va_s112 := va_lemma_PUSH(va_b111, va_s111, va_s106, va_op_word_reg(EDI));
      ghost var new_flags := va_get_reg(EDI, va_s112);
      Lemma_SetBit_Associative(USBTD_SLOT_FLAG_SlotSecure_Bit, USBTD_SLOT_FLAG_SubmitDone_Bit);
      Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);
      assert TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit);  // line 237 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      ghost var va_b117, va_s117 := va_lemma_Load(va_b112, va_s112, va_s106, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
      ghost var va_b118, va_s118 := va_lemma_PUSH(va_b117, va_s117, va_s106, va_op_word_reg(EDI));
      assert va_get_reg(EDI, va_s118) == in_td_slot;  // line 240 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      ghost var va_b120, va_s120 := va_lemma_usbtd_set_flags(va_b118, va_s118, va_s106);
      ghost var va_b121, va_s121 := va_lemma_POP_VOID(va_b120, va_s120, va_s106, 2 *
        ARCH_WORD_BYTES);
      assert va_get_reg(ESP, va_s121) == orig_esp;  // line 243 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      ghost var globals4 := va_get_globals(va_s121);
      Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(in_td_slot,
        G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset);
      Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals3, globals4, in_td_slot,
        G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
      Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals3, globals4, in_td_slot,
        G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
      Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals3, globals4, in_td_slot,
        G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
      Lemma_WK_USB_TD_Map_PreserveOtherNonScratchpadGVarsIfModifyAnyUSBTDFields(globals3, globals4,
        in_td_slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
      Lemma__usbtd_slot_submit_and_verify_qh32_inner_ProveProperty1(va_get_globals(va_old_s),
        globals1, globals3, globals4, in_td_slot);
      Lemma__usbtd_slot_submit_and_verify_qh32_inner_ProveProperty2(globals3, globals4, in_td_slot);
      ghost var va_b131, va_s131 := va_lemma_Store(va_b121, va_s121, va_s106, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      va_s106 := va_lemma_empty(va_s131, va_s106);
    }
    else
    {
      ghost var va_b132 := va_get_block(va_get_ifFalse(va_c106));
      assert usbtd_temp_get_pid(globals1) == usbtd_temp_get_pid(va_get_globals(va_s107));  // line 260 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      assert usbtd_map_get_pid(va_get_globals(va_old_s), in_td_slot) ==
        usbtd_temp_get_pid(va_get_globals(va_s107));  // line 261 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      assert usbtd_temp_valid_pid(globals3);  // line 263 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      assert usbtd_temp_valid_type(globals3);  // line 264 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      assert usbtd_temp_valid_busid(globals3);  // line 265 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      assert usbtd_temp_valid_wimpdrv_slotid(globals3);  // line 266 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      assert usbtd_temp_valid_usbpdev_slotid(globals3);  // line 267 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      assert usbtd_temp_get_flags(globals3) == 0;  // line 269 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      assert usbtd_map_get_flags(globals3, in_td_slot) == SetBit(0,
        USBTD_SLOT_FLAG_SubmitDone_Bit);  // line 270 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      Lemma_TestBit_ReturnFalseIfANumberIs0();
      Lemma_TestBit_ReturnFalse_IfBitNotSetAndAfterSetOtherBits(USBTD_SLOT_FLAG_SlotSecure_Bit);
      assert TestBit(usbtd_map_get_flags(globals3, in_td_slot), USBTD_SLOT_FLAG_SlotSecure_Bit) ==
        false;  // line 273 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      ghost var va_b145, va_s145 := va_lemma_Load(va_b132, va_s107, va_s106, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
      ghost var va_b146, va_s146 := va_lemma_PUSH(va_b145, va_s145, va_s106, va_op_word_reg(EDI));
      assert eehci_mem_no_ref_to_usbtd_slot(globals3, in_td_slot);  // line 278 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      ghost var va_b148, va_s148 := va_lemma_CALL_USBTD_Restore(va_b146, va_s146, va_s106);
      ghost var va_b149, va_s149 := va_lemma_POP_VOID(va_b148, va_s148, va_s106, 1 *
        ARCH_WORD_BYTES);
      assert va_get_reg(ESP, va_s149) == orig_esp;  // line 281 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      assert ffi_usbtd_restore_stack_and_globals_inner(globals2, va_get_globals(va_s149),
        in_td_slot);  // line 283 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      Lemma_USBTD_BackupAndRestore_ResultsInOriginalNonScratchpadGlobalVars(va_get_globals(va_old_s),
        globals1, globals2, va_get_globals(va_s149), in_td_slot);
      assert global_non_scratchpad_vars_are_unchanged(va_get_globals(va_old_s),
        va_get_globals(va_s149));  // line 285 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
      ghost var va_b154, va_s154 := va_lemma_Store(va_b149, va_s149, va_s106, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      va_s106 := va_lemma_empty(va_s154, va_s106);
    }
    va_s78 := va_lemma_empty(va_s106, va_s78);
  }
  else
  {
    ghost var va_b155 := va_get_block(va_get_ifFalse(va_c78));
    ghost var va_b156, va_s156 := va_lemma_Store(va_b155, va_s79, va_s78, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert global_non_scratchpad_vars_are_unchanged(va_get_globals(va_old_s),
      va_get_globals(va_s156));  // line 293 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
    va_s78 := va_lemma_empty(va_s156, va_s78);
  }
  ghost var va_b158, va_s158 := va_lemma_POP_Reg1ToReg6(va_b78, va_s78, va_sM);
  ghost var va_b159, va_s159 := va_lemma_POP_OneReg(va_b158, va_s158, va_sM, va_op_reg_reg(EBP));
  assert is_flags_unchanged(va_get_sreg(EFLAGS, va_old_s), va_get_sreg(EFLAGS, va_s159));  // line 299 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.vad
  Lemma_x86_IfEFlagsIsUnchanged_ThenSRegsIsUnchanged(va_old_s, va_s159, va_get_sreg(EFLAGS,
    va_old_s), va_get_sreg(EFLAGS, va_s159));
  Lemma_modify_regs_stateeq(va_old_s, va_s159);
  va_sM := va_lemma_empty(va_s159, va_sM);
}
//--
lemma Lemma_usbtd_slot_submit_and_verify_qh32_inner_impl_ProveIDUniquenessForTempUSBTD(
    globals1:globalsmap, globals2:globalsmap, globals3:globalsmap, td_slot:uint32
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(globals3)

    requires forall i :: usbtd_map_valid_slot_id(i) && i != td_slot &&
                usbtd_map_get_idword(globals1, i) != USBTD_ID_INVALID
            ==> usbtd_map_get_idword(globals1, i) != usbtd_temp_get_id(globals1)

    requires usbtd_map_valid_slot_id(td_slot)
    requires p_usbtd_slot_submit_usbtd_ret_global(globals1, globals2, td_slot)
    requires globals2 == globals3

    ensures forall i :: usbtd_map_valid_slot_id(i) && i != td_slot &&
                usbtd_map_get_idword(globals3, i) != USBTD_ID_INVALID
            ==> usbtd_map_get_idword(globals3, i) != usbtd_temp_get_id(globals3)
{
    reveal p_usbtd_equal();
}

// Prove the property 1 of <_usbtd_slot_submit_and_verify_qh32_inner>
lemma Lemma__usbtd_slot_submit_and_verify_qh32_inner_ProveProperty1(
    old_globals:globalsmap, globals1:globalsmap, globals2:globalsmap, new_globals:globalsmap, slot:uint32
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbtd_map_valid_slot_id(slot)

    requires global_non_scratchpad_vars_are_unchanged(old_globals, globals1)

    requires p_usbtd_slot_submit_usbtd_ret_global(globals1, globals2, slot)
    requires globals_other_gvar_unchanged_2vars(globals2, new_globals, G_USBTD_MAP_MEM(), G_Temp_USBTD())

    requires forall i :: usbtd_map_valid_slot_id(i) && i != slot
                ==> p_usbtd_equal(globals2, new_globals, i)
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_pid(globals2, i) == usbtd_map_get_pid(new_globals, i)

    ensures usbtd_map_modify_one_usbtd_and_temp_usbtd_only(old_globals, new_globals, slot)
    ensures usbtd_map_get_pid(old_globals, slot) == usbtd_map_get_pid(new_globals, slot)
{
    reveal global_non_scratchpad_vars_are_unchanged();

    // Prove p_usbtd_equal
    forall i:uint32 | usbtd_map_valid_slot_id(i) && i != slot
        ensures p_usbtd_equal(old_globals, new_globals, i)
    {
        Lemma_global_non_scratchpad_vars_are_unchanged_ImpliesEqualUSBTDs(old_globals, globals1);
        Lemma_p_usbtd_equal_transitive(old_globals, globals1, globals2, i);
        Lemma_p_usbtd_equal_transitive(old_globals, globals2, new_globals, i);
        
        assert p_usbtd_equal(old_globals, globals1, i);
        assert p_usbtd_equal(old_globals, globals2, i);
        assert p_usbtd_equal(globals2, new_globals, i);
        assert p_usbtd_equal(old_globals, new_globals, i);
    }
}

// Prove the property 2 of <_usbtd_slot_submit_and_verify_qh32_inner>
lemma Lemma__usbtd_slot_submit_and_verify_qh32_inner_ProveProperty2(
    globals2:globalsmap, new_globals:globalsmap, slot:uint32
)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbtd_map_valid_slot_id(slot)

    requires usbtd_map_get_type(globals2, slot) == USBTDs_TYPE_QH32

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_type(globals2, i) == usbtd_map_get_type(new_globals, i)

    ensures usbtd_map_get_type(new_globals, slot) == USBTDs_TYPE_QH32
{
    reveal global_non_scratchpad_vars_are_unchanged();
}
