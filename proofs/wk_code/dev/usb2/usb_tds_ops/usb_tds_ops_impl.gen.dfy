include "../../../ins/x86/ins_wrapper.gen.dfy"
include "../usb_tds_utils.gen.dfy"
include "../../../partition_id_ops.gen.dfy"
include "../eehci_info.gen.dfy"
include "../../../drv/drv_ops_utils.gen.dfy"
include "..\\state_mapping\\usbtd_map.s.dfy"
include "..\\usb_tds_utils.i.dfy"
include "usb_tds_ops.dafny21.gen.dfy"
include "usb_tds_ops.private.gen.dfy"
//-- _usbtd_slot_allocate_1slot_private
//--
//-- _usbtd_slot_submit
//--
//-- USBTD_slot_allocate_1slot_Impl

function method{:opaque} va_code_USBTD_slot_allocate_1slot_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_code_PUSH_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_usbtd_id_generate(va_op_reg_reg(EAX)), va_CCons(va_code_POP_VOID(2 *
    ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EAX),
    va_const_cmp(USBTD_ID_INVALID)), va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code__usbtd_slot_allocate_1slot_private(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_op_word_reg(EBX)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), ARCH_WORD_BYTES),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES, va_op_word_reg(EDI)),
    va_CCons(va_code_POP_VOID(3 * ARCH_WORD_BYTES), va_CNil())))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(USBTD_SlotID_INVALID)), va_CNil())))),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))
}

lemma{:timeLimitMultiplier 30} va_lemma_USBTD_slot_allocate_1slot_Impl(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state, out_new_id:word)
  requires va_require(va_b0, va_code_USBTD_slot_allocate_1slot_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 14 *
    ARCH_WORD_BYTES + 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space)
    && (var stack_retval_space := 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_retval_space))
  requires var td_type:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); ((td_type == USBTDs_TYPE_QTD32 || td_type == USBTDs_TYPE_QH32) || td_type ==
    USBTDs_TYPE_iTD32) || td_type == USBTDs_TYPE_siTD32
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var td_type:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var slot:uint32 :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); ((((ret == TRUE ==>
    WS_PartitionID(pid) in pids_parse_g_wimp_pids(va_get_globals(va_s0))) && (ret == TRUE ==>
    usbtd_map_valid_slot_id(slot))) && (ret == TRUE ==> out_new_id != USBTD_ID_INVALID)) && (ret ==
    TRUE ==> (forall i:uint32 :: usbtd_map_valid_slot_id(i) &&
    usbtd_map_get_idword(va_get_globals(va_s0), i) != USBTD_ID_INVALID ==>
    usbtd_map_get_idword(va_get_globals(va_s0), i) != out_new_id))) &&
    usbtd_slot_allocate_1slot_globals_relationship(va_get_globals(va_s0), va_get_globals(va_sM),
    slot, out_new_id, td_type, pid, ret)
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
  reveal_va_code_USBTD_slot_allocate_1slot_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(EBX),
    va_op_reg_reg(EAX));
  ghost var va_b9, va_s9 := va_lemma_PUSH_VOID(va_b8, va_s8, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_b10, va_s10 := va_lemma_usbtd_id_generate(va_b9, va_s9, va_sM, va_op_reg_reg(EAX));
  ghost var va_b11, va_s11 := va_lemma_POP_VOID(va_b10, va_s10, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s12, va_c12, va_b12 := va_lemma_block(va_b11, va_s11, va_sM);
  ghost var va_cond_c12, va_s13:va_state := va_lemma_ifElse(va_get_ifCond(va_c12),
    va_get_ifTrue(va_c12), va_get_ifFalse(va_c12), va_s11, va_s12);
  if (va_cond_c12)
  {
    ghost var va_b14 := va_get_block(va_get_ifTrue(va_c12));
    ghost var globals1 := va_get_globals(va_s13);
    Lemma_usbtd_id_generate_ProveIDUniqueness(globals1, va_get_reg(EAX, va_s13));
    assert globals_other_gvar_unchanged(va_get_globals(va_old_s), globals1, G_USBTD_ID_Counter()); 
      // line 105 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    out_new_id := va_get_reg(EAX, va_s13);
    ghost var va_b19, va_s19 := va_lemma_PUSH(va_b14, va_s13, va_s12, va_op_word_reg(EAX));
    ghost var va_b20, va_s20 := va_lemma_Load(va_b19, va_s19, va_s12, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
    ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s20, va_s12, va_op_word_reg(EDI));
    ghost var td_type := va_get_reg(EDI, va_s21);
    ghost var va_b23, va_s23 := va_lemma_Load(va_b21, va_s21, va_s12, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
    ghost var va_b24, va_s24 := va_lemma_PUSH(va_b23, va_s23, va_s12, va_op_word_reg(EDI));
    ghost var pid := va_get_reg(EDI, va_s24);
    ghost var va_b26, va_s26 := va_lemma__usbtd_slot_allocate_1slot_private(va_b24, va_s24, va_s12);
    ghost var va_b27, va_s27 := va_lemma_Load(va_b26, va_s26, va_s12, va_op_word_reg(EBX),
      va_op_word_reg(ESP), 0);
    ghost var va_b28, va_s28 := va_lemma_Store(va_b27, va_s27, va_s12, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_op_word_reg(EBX));
    ghost var va_b29, va_s29 := va_lemma_Load(va_b28, va_s28, va_s12, va_op_word_reg(EDI),
      va_op_word_reg(ESP), ARCH_WORD_BYTES);
    ghost var va_b30, va_s30 := va_lemma_Store(va_b29, va_s29, va_s12, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_op_word_reg(EDI));
    ghost var va_b31, va_s31 := va_lemma_POP_VOID(va_b30, va_s30, va_s12, 3 * ARCH_WORD_BYTES);
    ghost var td_slot := va_get_reg(EDI, va_s31);
    if (va_get_reg(EBX, va_s31) == TRUE)
    {
      ghost var globals2 := va_get_globals(va_s31);
      assert p_usbtd_slot_allocate_1slot_private_globals_relationship(globals1, globals2, td_slot,
        va_get_reg(EAX, va_s31), td_type, pid, TRUE);  // line 127 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
      Lemma_usbtd_slot_allocate_1slot_ProveProperty2(va_get_globals(va_old_s), globals1, globals2,
        td_slot, va_get_reg(EAX, va_s31), td_type, pid);
    }
    va_s12 := va_lemma_empty(va_s31, va_s12);
  }
  else
  {
    ghost var va_b34 := va_get_block(va_get_ifFalse(va_c12));
    ghost var va_b35, va_s35 := va_lemma_Store(va_b34, va_s13, va_s12, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b36, va_s36 := va_lemma_Store(va_b35, va_s35, va_s12, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(USBTD_SlotID_INVALID));
    va_s12 := va_lemma_empty(va_s36, va_s12);
  }
  ghost var va_b37, va_s37 := va_lemma_POP_TwoRegs(va_b12, va_s12, va_sM, va_op_reg_reg(EBX),
    va_op_reg_reg(EAX));
  ghost var va_b38, va_s38 := va_lemma_POP_OneReg(va_b37, va_s37, va_sM, va_op_reg_reg(EDI));
  ghost var va_b39, va_s39 := va_lemma_POP_OneReg(va_b38, va_s38, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s39, va_sM);
}
//--
//-- USBTD_slot_deallocate_1slot_Impl

function method{:opaque} va_code_USBTD_slot_deallocate_1slot_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_usbtd_check_td_slot_id(va_op_reg_reg(EDI), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_usbtd_get_td_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code__usbtd_find_referencing_secure_slot(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_CALL_EEHCI_FIND_RefToUSBTD(), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(eEHCI_SlotID_EMPTY)),
    va_Block(va_CCons(va_code_PUSH(va_const_word(0)), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_usbtd_set_flags(), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_const_word(PID_INVALID)), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_usbtd_set_td_pid(), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil()))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))
}

lemma{:timeLimitMultiplier 40} va_lemma_USBTD_slot_deallocate_1slot_Impl(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_USBTD_slot_deallocate_1slot_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 10 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + FFI_USBTD_IsRefTargetUSBTD_StackParamsWords * ARCH_WORD_BYTES
    + 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_retval_space := 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_retval_space))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var td_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((((ret == TRUE ==>
    usbtd_map_valid_slot_id(td_slot)) && (ret == TRUE ==>
    pids_is_existing_wimp_pid(va_get_globals(va_s0), usbtd_map_get_pid(va_get_globals(va_s0),
    td_slot).v))) && (ret == TRUE ==> eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_s0),
    td_slot))) && (ret == TRUE ==> usbtds_verifiedtds_do_not_associate_usbtd(va_get_globals(va_s0),
    td_slot))) && usbtd_slot_deallocate_1slot_globals_relationship(va_get_globals(va_s0),
    va_get_globals(va_sM), td_slot, ret)
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
  reveal_va_code_USBTD_slot_deallocate_1slot_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b9, va_s9 := va_lemma_Load(va_b8, va_s8, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var in_td_slot := va_get_reg(EDI, va_s9);
  ghost var va_b11, va_s11 := va_lemma_usbtd_check_td_slot_id(va_b9, va_s9, va_sM,
    va_op_reg_reg(EDI), va_op_reg_reg(EAX));
  ghost var va_s12, va_c12, va_b12 := va_lemma_block(va_b11, va_s11, va_sM);
  ghost var va_cond_c12, va_s13:va_state := va_lemma_ifElse(va_get_ifCond(va_c12),
    va_get_ifTrue(va_c12), va_get_ifFalse(va_c12), va_s11, va_s12);
  if (va_cond_c12)
  {
    ghost var va_b14 := va_get_block(va_get_ifTrue(va_c12));
    ghost var va_b15, va_s15 := va_lemma_PUSH(va_b14, va_s13, va_s12, va_op_word_reg(EDI));
    ghost var va_b16, va_s16 := va_lemma_usbtd_get_td_pid(va_b15, va_s15, va_s12);
    ghost var va_b17, va_s17 := va_lemma_Load(va_b16, va_s16, va_s12, va_op_word_reg(EDX),
      va_op_word_reg(ESP), 0);
    ghost var va_b18, va_s18 := va_lemma_POP_VOID(va_b17, va_s17, va_s12, 1 * ARCH_WORD_BYTES);
    ghost var va_b19, va_s19 := va_lemma_PUSH_VOID(va_b18, va_s18, va_s12, 1 * ARCH_WORD_BYTES);
    ghost var va_b20, va_s20 := va_lemma_PUSH(va_b19, va_s19, va_s12, va_op_word_reg(EDX));
    ghost var va_b21, va_s21 := va_lemma_pids_is_existing_wimp_pid(va_b20, va_s20, va_s12);
    ghost var va_b22, va_s22 := va_lemma_Load(va_b21, va_s21, va_s12, va_op_word_reg(EAX),
      va_op_word_reg(ESP), 0);
    ghost var va_b23, va_s23 := va_lemma_POP_VOID(va_b22, va_s22, va_s12, 2 * ARCH_WORD_BYTES);
    ghost var va_s24, va_c24, va_b24 := va_lemma_block(va_b23, va_s23, va_s12);
    ghost var va_cond_c24, va_s25:va_state := va_lemma_ifElse(va_get_ifCond(va_c24),
      va_get_ifTrue(va_c24), va_get_ifFalse(va_c24), va_s23, va_s24);
    if (va_cond_c24)
    {
      ghost var va_b26 := va_get_block(va_get_ifTrue(va_c24));
      ghost var va_b27, va_s27 := va_lemma_PUSH_VOID(va_b26, va_s25, va_s24, 1 * ARCH_WORD_BYTES);
      ghost var va_b28, va_s28 := va_lemma_PUSH(va_b27, va_s27, va_s24, va_op_word_reg(EDI));
      ghost var va_b29, va_s29 := va_lemma__usbtd_find_referencing_secure_slot(va_b28, va_s28,
        va_s24);
      ghost var va_b30, va_s30 := va_lemma_Load(va_b29, va_s29, va_s24, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b31, va_s31 := va_lemma_POP_VOID(va_b30, va_s30, va_s24, 2 * ARCH_WORD_BYTES);
      ghost var va_s32, va_c32, va_b32 := va_lemma_block(va_b31, va_s31, va_s24);
      ghost var va_cond_c32, va_s33:va_state := va_lemma_ifElse(va_get_ifCond(va_c32),
        va_get_ifTrue(va_c32), va_get_ifFalse(va_c32), va_s31, va_s32);
      if (va_cond_c32)
      {
        ghost var va_b34 := va_get_block(va_get_ifTrue(va_c32));
        Lemma_InstSaneState_usbtd_find_referencing_secure_slot_ReturnFalseImplies_usbtds_verifiedtds_do_not_associate_usbtd(va_get_globals(va_s33),
          va_get_reg(EDI, va_s33));
        ghost var va_b36, va_s36 := va_lemma_PUSH(va_b34, va_s33, va_s32, va_op_word_reg(EDI));
        ghost var old_wkm := va_s36.wk_mstate;
        ghost var va_b38, va_s38 := va_lemma_CALL_EEHCI_FIND_RefToUSBTD(va_b36, va_s36, va_s32);
        ghost var new_stack1 := va_get_mem(va_s38);
        ghost var va_b40, va_s40 := va_lemma_Load(va_b38, va_s38, va_s32, va_op_word_reg(ESI),
          va_op_word_reg(ESP), 0);
        ghost var va_b41, va_s41 := va_lemma_POP_VOID(va_b40, va_s40, va_s32, 1 * ARCH_WORD_BYTES);
        ghost var va_b42, va_s42 := va_lemma_Load(va_b41, va_s41, va_s32, va_op_word_reg(EDI),
          va_op_word_reg(EBP), ARCH_WORD_BYTES);
        ghost var va_s43, va_c43, va_b43 := va_lemma_block(va_b42, va_s42, va_s32);
        ghost var va_cond_c43, va_s44:va_state := va_lemma_ifElse(va_get_ifCond(va_c43),
          va_get_ifTrue(va_c43), va_get_ifFalse(va_c43), va_s42, va_s43);
        if (va_cond_c43)
        {
          ghost var va_b45 := va_get_block(va_get_ifTrue(va_c43));
          Lemma_eehci_find_ref_to_usbtd_property(old_wkm, new_stack1);
          assert forall i:uint32 :: eehci_valid_slot_id(i) ==>
            EECHI_DoNotRefGivenUSBTD(va_get_globals(va_s44), i, va_get_reg(EDI, va_s44));  // line 251 column 21 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
          assert eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_s44), va_get_reg(EDI, va_s44)); 
            // line 253 column 21 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
          ghost var globals1 := va_get_globals(va_s44);
          assert globals1 == va_get_globals(va_old_s);  // line 255 column 21 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
          ghost var va_b51, va_s51 := va_lemma_PUSH(va_b45, va_s44, va_s43, va_const_word(0));
          ghost var va_b52, va_s52 := va_lemma_PUSH(va_b51, va_s51, va_s43, va_op_word_reg(EDI));
          Lemma_TestBit_ReturnFalseIfANumberIs0();
          assert TestBit(0, USBTD_SLOT_FLAG_SlotSecure_Bit) == false;  // line 261 column 21 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
          ghost var va_b55, va_s55 := va_lemma_usbtd_set_flags(va_b52, va_s52, va_s43);
          ghost var va_b56, va_s56 := va_lemma_POP_VOID(va_b55, va_s55, va_s43, 2 *
            ARCH_WORD_BYTES);
          ghost var globals2 := va_get_globals(va_s56);
          Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals1, globals2, in_td_slot,
            G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, 0);
          Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(globals1, globals2,
            in_td_slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, 0);
          assert global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2,
            G_EEHCI_MEM());  // line 268 column 21 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
          assert global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2,
            G_Existing_PIDs());  // line 269 column 21 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
          Lemma_eehci_mem_no_ref_to_usbtd_slot_Equivilant(globals1, globals2, va_get_reg(EDI,
            va_s56));
          ghost var va_b63, va_s63 := va_lemma_PUSH(va_b56, va_s56, va_s43,
            va_const_word(PID_INVALID));
          ghost var va_b64, va_s64 := va_lemma_PUSH(va_b63, va_s63, va_s43, va_op_word_reg(EDI));
          ghost var va_b65, va_s65 := va_lemma_usbtd_set_td_pid(va_b64, va_s64, va_s43);
          ghost var va_b66, va_s66 := va_lemma_POP_VOID(va_b65, va_s65, va_s43, 2 *
            ARCH_WORD_BYTES);
          Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(in_td_slot,
            G_USBTDs_MAP_ENTRY_PID_BytesOffset);
          Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals2,
            va_get_globals(va_s66), in_td_slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset, PID_INVALID);
          Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals2, va_get_globals(va_s66),
            in_td_slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset, PID_INVALID);
          Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(globals2,
            va_get_globals(va_s66), in_td_slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset, PID_INVALID);
          ghost var va_b71, va_s71 := va_lemma_Store(va_b66, va_s66, va_s43, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          forall i:uint32
            | usbtd_map_valid_slot_id(i) && i != in_td_slot
            ensures p_usbtd_equal(va_get_globals(va_old_s), va_get_globals(va_s71), i)
          {
            assert globals1 == va_get_globals(va_old_s);  // line 290 column 25 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
            Lemma_p_usbtd_equal_transitive(globals1, globals2, va_get_globals(va_s71), i);
          }
          Lemma_p_usbtd_content_equal_transitive(globals1, globals2, va_get_globals(va_s71),
            in_td_slot);
          va_s43 := va_lemma_empty(va_s71, va_s43);
        }
        else
        {
          ghost var va_b74 := va_get_block(va_get_ifFalse(va_c43));
          ghost var va_b75, va_s75 := va_lemma_Store(va_b74, va_s44, va_s43, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s75) == va_get_globals(va_old_s);  // line 300 column 21 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s75));
          va_s43 := va_lemma_empty(va_s75, va_s43);
        }
        va_s32 := va_lemma_empty(va_s43, va_s32);
      }
      else
      {
        ghost var va_b78 := va_get_block(va_get_ifFalse(va_c32));
        ghost var va_b79, va_s79 := va_lemma_Store(va_b78, va_s33, va_s32, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s79) == va_get_globals(va_old_s);  // line 308 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s79));
        va_s32 := va_lemma_empty(va_s79, va_s32);
      }
      va_s24 := va_lemma_empty(va_s32, va_s24);
    }
    else
    {
      ghost var va_b82 := va_get_block(va_get_ifFalse(va_c24));
      ghost var va_b83, va_s83 := va_lemma_Store(va_b82, va_s25, va_s24, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s83) == va_get_globals(va_old_s);  // line 316 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s83));
      va_s24 := va_lemma_empty(va_s83, va_s24);
    }
    va_s12 := va_lemma_empty(va_s24, va_s12);
  }
  else
  {
    ghost var va_b86 := va_get_block(va_get_ifFalse(va_c12));
    ghost var va_b87, va_s87 := va_lemma_Store(va_b86, va_s13, va_s12, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s87) == va_get_globals(va_old_s);  // line 324 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s87));
    va_s12 := va_lemma_empty(va_s87, va_s12);
  }
  ghost var va_b90, va_s90 := va_lemma_POP_Reg1ToReg6(va_b12, va_s12, va_sM);
  ghost var va_b91, va_s91 := va_lemma_POP_OneReg(va_b90, va_s90, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s91, va_sM);
}
//--
//-- _usbtd_slot_submit_and_verify_morechecks

function method{:opaque} va_code__usbtd_slot_submit_and_verify_morechecks():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(ECX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_usbtd_check_td_slot_id(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_pids_is_existing_wimp_pid(), va_CCons(va_code_Load(va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_usbtd_get_td_pid(),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil())))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 10} va_lemma__usbtd_slot_submit_and_verify_morechecks(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbtd_slot_submit_and_verify_morechecks(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1
    * ARCH_WORD_BYTES); var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); (((ret ==
    TRUE ==> usbtd_map_valid_slot_id(td_slot)) && (ret == TRUE ==>
    wimpdrv_valid_slot_id(wimpdrv_slot_id))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot_id) in
    pids_parse_g_wimp_pids(va_get_globals(va_s0)))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot_id) ==
    usbtd_map_get_pid(va_get_globals(va_s0), td_slot))
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code__usbtd_slot_submit_and_verify_morechecks();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_wimpdrv_check_slotid(va_b11, va_s11, va_sM,
    va_op_reg_reg(ECX), va_op_reg_reg(EAX));
  ghost var va_s13, va_c13, va_b13 := va_lemma_block(va_b12, va_s12, va_sM);
  ghost var va_cond_c13, va_s14:va_state := va_lemma_ifElse(va_get_ifCond(va_c13),
    va_get_ifTrue(va_c13), va_get_ifFalse(va_c13), va_s12, va_s13);
  if (va_cond_c13)
  {
    ghost var va_b15 := va_get_block(va_get_ifTrue(va_c13));
    ghost var va_b16, va_s16 := va_lemma_usbtd_check_td_slot_id(va_b15, va_s14, va_s13,
      va_op_reg_reg(EBX), va_op_reg_reg(EAX));
    ghost var va_s17, va_c17, va_b17 := va_lemma_block(va_b16, va_s16, va_s13);
    ghost var va_cond_c17, va_s18:va_state := va_lemma_ifElse(va_get_ifCond(va_c17),
      va_get_ifTrue(va_c17), va_get_ifFalse(va_c17), va_s16, va_s17);
    if (va_cond_c17)
    {
      ghost var va_b19 := va_get_block(va_get_ifTrue(va_c17));
      ghost var va_b20, va_s20 := va_lemma_PUSH(va_b19, va_s18, va_s17, va_op_word_reg(ECX));
      ghost var va_b21, va_s21 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b20, va_s20, va_s17);
      ghost var va_b22, va_s22 := va_lemma_Load(va_b21, va_s21, va_s17, va_op_word_reg(EDI),
        va_op_word_reg(ESP), 0);
      ghost var va_b23, va_s23 := va_lemma_POP_VOID(va_b22, va_s22, va_s17, 1 * ARCH_WORD_BYTES);
      ghost var va_b24, va_s24 := va_lemma_PUSH_VOID(va_b23, va_s23, va_s17, 1 * ARCH_WORD_BYTES);
      ghost var va_b25, va_s25 := va_lemma_PUSH(va_b24, va_s24, va_s17, va_op_word_reg(EDI));
      ghost var va_b26, va_s26 := va_lemma_pids_is_existing_wimp_pid(va_b25, va_s25, va_s17);
      ghost var va_b27, va_s27 := va_lemma_Load(va_b26, va_s26, va_s17, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b28, va_s28 := va_lemma_POP_VOID(va_b27, va_s27, va_s17, 2 * ARCH_WORD_BYTES);
      ghost var va_s29, va_c29, va_b29 := va_lemma_block(va_b28, va_s28, va_s17);
      ghost var va_cond_c29, va_s30:va_state := va_lemma_ifElse(va_get_ifCond(va_c29),
        va_get_ifTrue(va_c29), va_get_ifFalse(va_c29), va_s28, va_s29);
      if (va_cond_c29)
      {
        ghost var va_b31 := va_get_block(va_get_ifTrue(va_c29));
        ghost var va_b32, va_s32 := va_lemma_PUSH(va_b31, va_s30, va_s29, va_op_word_reg(EBX));
        ghost var va_b33, va_s33 := va_lemma_usbtd_get_td_pid(va_b32, va_s32, va_s29);
        ghost var va_b34, va_s34 := va_lemma_Load(va_b33, va_s33, va_s29, va_op_word_reg(ESI),
          va_op_word_reg(ESP), 0);
        ghost var va_b35, va_s35 := va_lemma_POP_VOID(va_b34, va_s34, va_s29, 1 * ARCH_WORD_BYTES);
        ghost var va_s36, va_c36, va_b36 := va_lemma_block(va_b35, va_s35, va_s29);
        ghost var va_cond_c36, va_s37:va_state := va_lemma_ifElse(va_get_ifCond(va_c36),
          va_get_ifTrue(va_c36), va_get_ifFalse(va_c36), va_s35, va_s36);
        if (va_cond_c36)
        {
          ghost var va_b38 := va_get_block(va_get_ifTrue(va_c36));
          ghost var va_b39, va_s39 := va_lemma_Store(va_b38, va_s37, va_s36, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          va_s36 := va_lemma_empty(va_s39, va_s36);
        }
        else
        {
          ghost var va_b40 := va_get_block(va_get_ifFalse(va_c36));
          ghost var va_b41, va_s41 := va_lemma_Store(va_b40, va_s37, va_s36, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s41) == va_get_globals(va_old_s);  // line 432 column 21 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s41));
          va_s36 := va_lemma_empty(va_s41, va_s36);
        }
        va_s29 := va_lemma_empty(va_s36, va_s29);
      }
      else
      {
        ghost var va_b44 := va_get_block(va_get_ifFalse(va_c29));
        ghost var va_b45, va_s45 := va_lemma_Store(va_b44, va_s30, va_s29, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s45) == va_get_globals(va_old_s);  // line 440 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s45));
        va_s29 := va_lemma_empty(va_s45, va_s29);
      }
      va_s17 := va_lemma_empty(va_s29, va_s17);
    }
    else
    {
      ghost var va_b48 := va_get_block(va_get_ifFalse(va_c17));
      ghost var va_b49, va_s49 := va_lemma_Store(va_b48, va_s18, va_s17, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s49) == va_get_globals(va_old_s);  // line 448 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s49));
      va_s17 := va_lemma_empty(va_s49, va_s17);
    }
    va_s13 := va_lemma_empty(va_s17, va_s13);
  }
  else
  {
    ghost var va_b52 := va_get_block(va_get_ifFalse(va_c13));
    ghost var va_b53, va_s53 := va_lemma_Store(va_b52, va_s14, va_s13, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s53) == va_get_globals(va_old_s);  // line 456 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s53));
    va_s13 := va_lemma_empty(va_s53, va_s13);
  }
  ghost var va_b56, va_s56 := va_lemma_POP_Reg1ToReg6(va_b13, va_s13, va_sM);
  ghost var va_b57, va_s57 := va_lemma_POP_OneReg(va_b56, va_s56, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s57, va_sM);
}
//--
//-- _usbtd_slot_allocate_1slot_private

function method{:opaque} va_code__usbtd_slot_allocate_1slot_private():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ECX)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI),
    va_const_word(TRUE)), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_usbtd_find_empty_slot(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_const_word(0)), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_usbtd_set_flags(), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(ECX)), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_usbtd_set_id(), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_usbtd_set_td_pid(), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(ECX)), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_usbtd_set_td_type(), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_CALL_USBTD_Clear_Content(),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES, va_op_word_reg(EAX)),
    va_CNil()))))))))))))))))))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_const_word(USBTD_SlotID_INVALID)), va_CNil())))), va_CNil()))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(USBTD_SlotID_INVALID)), va_CNil())))),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))
}

lemma{:timeLimitMultiplier 110} va_lemma__usbtd_slot_allocate_1slot_private(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbtd_slot_allocate_1slot_private(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 6 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 2 *
    ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space)
    && (var stack_retval_space := 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_retval_space))
  requires var td_type:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); ((td_type == USBTDs_TYPE_QTD32 || td_type == USBTDs_TYPE_QH32) || td_type ==
    USBTDs_TYPE_iTD32) || td_type == USBTDs_TYPE_siTD32
  requires var usbtd_idword:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); ((forall i:uint32 :: usbtd_map_valid_slot_id(i) &&
    usbtd_map_get_idword(va_get_globals(va_s0), i) != USBTD_ID_INVALID ==>
    usbtd_map_get_idword(va_get_globals(va_s0), i) != usbtd_idword) && usbtd_idword <=
    usbtd_id_counter_read(va_get_globals(va_s0))) && usbtd_idword != USBTD_ID_INVALID
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var usbtd_idword:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); var td_type:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var slot:uint32 :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); ((((ret == TRUE ==>
    WS_PartitionID(pid) in pids_parse_g_wimp_pids(va_get_globals(va_s0))) && (ret == TRUE ==>
    usbtd_map_valid_slot_id(slot))) && (ret == TRUE ==> usbtd_map_get_pid(va_get_globals(va_s0),
    slot) == WS_PartitionID(PID_INVALID))) && (ret == TRUE ==>
    eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_sM), slot))) &&
    p_usbtd_slot_allocate_1slot_private_globals_relationship(va_get_globals(va_s0),
    va_get_globals(va_sM), slot, usbtd_idword, td_type, pid, ret)
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
  reveal_va_code__usbtd_slot_allocate_1slot_private();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b10, va_s10 := va_lemma_PUSH_TwoRegs(va_b9, va_s9, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EBX));
  ghost var va_b11, va_s11 := va_lemma_PUSH_OneReg(va_b10, va_s10, va_sM, va_op_reg_reg(ECX));
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_MOV_ToReg(va_b12, va_s12, va_sM, va_op_reg_reg(ESI),
    va_const_word(TRUE));
  ghost var va_b14, va_s14 := va_lemma_PUSH_VOID(va_b13, va_s13, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b15, va_s15 := va_lemma_PUSH(va_b14, va_s14, va_sM, va_op_word_reg(EDI));
  ghost var va_b16, va_s16 := va_lemma_pids_is_existing_wimp_pid(va_b15, va_s15, va_sM);
  ghost var va_b17, va_s17 := va_lemma_Load(va_b16, va_s16, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(ESP), 0);
  ghost var va_b18, va_s18 := va_lemma_POP_VOID(va_b17, va_s17, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s19, va_c19, va_b19 := va_lemma_block(va_b18, va_s18, va_sM);
  ghost var va_cond_c19, va_s20:va_state := va_lemma_ifElse(va_get_ifCond(va_c19),
    va_get_ifTrue(va_c19), va_get_ifFalse(va_c19), va_s18, va_s19);
  if (va_cond_c19)
  {
    ghost var va_b21 := va_get_block(va_get_ifTrue(va_c19));
    ghost var va_b22, va_s22 := va_lemma_usbtd_find_empty_slot(va_b21, va_s20, va_s19,
      va_op_reg_reg(EAX), va_op_reg_reg(EBX));
    ghost var va_s23, va_c23, va_b23 := va_lemma_block(va_b22, va_s22, va_s19);
    ghost var va_cond_c23, va_s24:va_state := va_lemma_ifElse(va_get_ifCond(va_c23),
      va_get_ifTrue(va_c23), va_get_ifFalse(va_c23), va_s22, va_s23);
    if (va_cond_c23)
    {
      ghost var va_b25 := va_get_block(va_get_ifTrue(va_c23));
      assert va_get_globals(va_s24) == va_get_globals(va_old_s);  // line 570 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
      assert usbtd_map_get_pid(va_get_globals(va_s24), va_get_reg(EAX, va_s24)) ==
        WS_PartitionID(PID_INVALID);  // line 571 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
      Lemma_InstSaneState_IfUSBTDIsInactive_Then_usbtds_verifiedtds_do_not_associate_usbtd(va_get_globals(va_s24),
        va_get_reg(EAX, va_s24));
      Lemma_usbtd_find_empty_slot_FoundSlotMustNotRefedInAnyEEHCI(va_get_globals(va_s24),
        va_get_reg(EAX, va_s24));
      ghost var globals1 := va_get_globals(va_s24);
      ghost var va_b31, va_s31 := va_lemma_PUSH(va_b25, va_s24, va_s23, va_const_word(0));
      ghost var va_b32, va_s32 := va_lemma_PUSH(va_b31, va_s31, va_s23, va_op_word_reg(EAX));
      Lemma_TestBit_ReturnFalseIfANumberIs0();
      assert TestBit(0, USBTD_SLOT_FLAG_SlotSecure_Bit) == false;  // line 581 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
      ghost var va_b35, va_s35 := va_lemma_usbtd_set_flags(va_b32, va_s32, va_s23);
      ghost var va_b36, va_s36 := va_lemma_POP_VOID(va_b35, va_s35, va_s23, 2 * ARCH_WORD_BYTES);
      ghost var globals2 := va_get_globals(va_s36);
      Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals1, globals2, va_get_reg(EAX,
        va_s36), G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, 0);
      Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals1, globals2, va_get_reg(EAX,
        va_s36), G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, 0);
      assert global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2,
        G_EEHCI_MEM());  // line 588 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
      assert global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2,
        G_Existing_PIDs());  // line 589 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
      Lemma_eehci_mem_no_ref_to_usbtd_slot_Equivilant(globals1, globals2, va_get_reg(EAX, va_s36));
      assert eehci_mem_no_ref_to_usbtd_slot(globals2, va_get_reg(EAX, va_s36));  // line 591 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
      ghost var va_b44, va_s44 := va_lemma_Load(va_b36, va_s36, va_s23, va_op_word_reg(ECX),
        va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
      ghost var va_b45, va_s45 := va_lemma_PUSH(va_b44, va_s44, va_s23, va_op_word_reg(ECX));
      ghost var idword := va_get_reg(ECX, va_s45);
      ghost var va_b47, va_s47 := va_lemma_PUSH(va_b45, va_s45, va_s23, va_op_word_reg(EAX));
      Lemma_usbtd_slot_allocate_1slot_private_ProvePreConditionsOfUSBTDSetID(va_get_globals(va_s47),
        va_get_reg(EAX, va_s47), idword);
      ghost var va_b49, va_s49 := va_lemma_usbtd_set_id(va_b47, va_s47, va_s23);
      ghost var va_b50, va_s50 := va_lemma_POP_VOID(va_b49, va_s49, va_s23, 2 * ARCH_WORD_BYTES);
      ghost var globals3 := va_get_globals(va_s50);
      Lemma_eehci_mem_no_ref_to_usbtd_slot_Equivilant(globals2, globals3, va_get_reg(EAX, va_s50));
      Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals2, globals3, va_get_reg(EAX,
        va_s50), G_USBTDs_MAP_ENTRY_ID_BytesOffset, idword);
      Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals2, globals3, va_get_reg(EAX,
        va_s50), G_USBTDs_MAP_ENTRY_ID_BytesOffset, idword);
      ghost var va_b55, va_s55 := va_lemma_PUSH(va_b50, va_s50, va_s23, va_op_word_reg(EDI));
      ghost var va_b56, va_s56 := va_lemma_PUSH(va_b55, va_s55, va_s23, va_op_word_reg(EAX));
      ghost var va_b57, va_s57 := va_lemma_usbtd_set_td_pid(va_b56, va_s56, va_s23);
      ghost var va_b58, va_s58 := va_lemma_POP_VOID(va_b57, va_s57, va_s23, 2 * ARCH_WORD_BYTES);
      ghost var globals4 := va_get_globals(va_s58);
      Lemma_eehci_mem_no_ref_to_usbtd_slot_Equivilant(globals3, globals4, va_get_reg(EAX, va_s58));
      Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals3, globals4, va_get_reg(EAX,
        va_s58), G_USBTDs_MAP_ENTRY_PID_BytesOffset, va_get_reg(EDI, va_s58));
      Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals3, globals4, va_get_reg(EAX,
        va_s58), G_USBTDs_MAP_ENTRY_PID_BytesOffset, va_get_reg(EDI, va_s58));
      Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals3, globals4, va_get_reg(EAX,
        va_s58), G_USBTDs_MAP_ENTRY_PID_BytesOffset, va_get_reg(EDI, va_s58));
      ghost var va_b64, va_s64 := va_lemma_Load(va_b58, va_s58, va_s23, va_op_word_reg(ECX),
        va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
      ghost var va_b65, va_s65 := va_lemma_PUSH(va_b64, va_s64, va_s23, va_op_word_reg(ECX));
      ghost var td_type := va_get_reg(ECX, va_s65);
      ghost var va_b67, va_s67 := va_lemma_PUSH(va_b65, va_s65, va_s23, va_op_word_reg(EAX));
      ghost var va_b68, va_s68 := va_lemma_usbtd_set_td_type(va_b67, va_s67, va_s23);
      ghost var va_b69, va_s69 := va_lemma_POP_VOID(va_b68, va_s68, va_s23, 2 * ARCH_WORD_BYTES);
      ghost var globals5 := va_get_globals(va_s69);
      Lemma_eehci_mem_no_ref_to_usbtd_slot_Equivilant(globals4, globals5, va_get_reg(EAX, va_s69));
      Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals4, globals5, va_get_reg(EAX,
        va_s69), G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, td_type);
      Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals4, globals5, va_get_reg(EAX,
        va_s69), G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, td_type);
      Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals4, globals5, va_get_reg(EAX,
        va_s69), G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, td_type);
      ghost var va_b75, va_s75 := va_lemma_PUSH_Reg1ToReg6(va_b69, va_s69, va_s23);
      ghost var va_b76, va_s76 := va_lemma_PUSH(va_b75, va_s75, va_s23, va_op_word_reg(ECX));
      ghost var va_b77, va_s77 := va_lemma_PUSH(va_b76, va_s76, va_s23, va_op_word_reg(EAX));
      ghost var va_b78, va_s78 := va_lemma_CALL_USBTD_Clear_Content(va_b77, va_s77, va_s23);
      ghost var va_b79, va_s79 := va_lemma_POP_VOID(va_b78, va_s78, va_s23, 2 * ARCH_WORD_BYTES);
      ghost var va_b80, va_s80 := va_lemma_POP_Reg1ToReg6(va_b79, va_s79, va_s23);
      ghost var va_b81, va_s81 := va_lemma_Store(va_b80, va_s80, va_s23, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      ghost var va_b82, va_s82 := va_lemma_Store(va_b81, va_s81, va_s23, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_op_word_reg(EAX));
      forall i:uint32
        | usbtd_map_valid_slot_id(i) && i != va_get_reg(EAX, va_s82)
        ensures p_usbtd_equal(va_get_globals(va_old_s), va_get_globals(va_s82), i)
      {
        assert globals1 == va_get_globals(va_old_s);  // line 646 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
        Lemma_p_usbtd_equal_transitive(globals1, globals2, globals3, i);
        Lemma_p_usbtd_equal_transitive(globals1, globals3, globals4, i);
        Lemma_p_usbtd_equal_transitive(globals1, globals4, globals5, i);
        Lemma_p_usbtd_equal_transitive(globals1, globals5, va_get_globals(va_s82), i);
      }
      Lemma_eehci_mem_no_ref_to_usbtd_slot_Equivilant(globals5, va_get_globals(va_s82),
        va_get_reg(EAX, va_s82));
      va_s23 := va_lemma_empty(va_s82, va_s23);
    }
    else
    {
      ghost var va_b85 := va_get_block(va_get_ifFalse(va_c23));
      ghost var va_b86, va_s86 := va_lemma_Store(va_b85, va_s24, va_s23, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b87, va_s87 := va_lemma_Store(va_b86, va_s86, va_s23, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_const_word(USBTD_SlotID_INVALID));
      va_s23 := va_lemma_empty(va_s87, va_s23);
    }
    va_s19 := va_lemma_empty(va_s23, va_s19);
  }
  else
  {
    ghost var va_b88 := va_get_block(va_get_ifFalse(va_c19));
    ghost var va_b89, va_s89 := va_lemma_Store(va_b88, va_s20, va_s19, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b90, va_s90 := va_lemma_Store(va_b89, va_s89, va_s19, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(USBTD_SlotID_INVALID));
    va_s19 := va_lemma_empty(va_s90, va_s19);
  }
  ghost var va_b91, va_s91 := va_lemma_POP_OneReg(va_b19, va_s19, va_sM, va_op_reg_reg(ECX));
  ghost var va_b92, va_s92 := va_lemma_POP_TwoRegs(va_b91, va_s91, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EBX));
  ghost var va_b93, va_s93 := va_lemma_POP_TwoRegs(va_b92, va_s92, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b94, va_s94 := va_lemma_POP_OneReg(va_b93, va_s93, va_sM, va_op_reg_reg(EBP));
  Lemma_modify_regs_stateeq(va_old_s, va_s94);
  va_sM := va_lemma_empty(va_s94, va_sM);
}
//--
//-- _usbtd_slot_submit

function method{:opaque} va_code__usbtd_slot_submit():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 6 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_CALL_USBTD_Copy_From_User(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(FFI_USBTD_CopyFromUser_StackParamsWords *
    ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_eechi_id_get_bus_id(),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(ESI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 9 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 8 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 7 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 10 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code__usbtd_slot_submit_partial_otherfields(), va_CCons(va_code_POP_VOID(7 *
    ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CNil())))))))))))))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))))
}

lemma{:timeLimitMultiplier 150} va_lemma__usbtd_slot_submit(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbtd_slot_submit(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ +
    FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0)
    - stack_req_space) && (var stack_params_space := 10 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    (usbtd_map_valid_slot_id(td_slot) && eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_s0),
    td_slot)) && usbtds_verifiedtds_do_not_associate_usbtd(va_get_globals(va_s0), td_slot)
  requires var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    TestBit(usbtd_map_get_flags(va_get_globals(va_s0), td_slot), USBTD_SLOT_FLAG_SlotSecure_Bit) ==
    false
  requires var usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 9 *
    ARCH_WORD_BYTES); usbpdev_slot == WimpUSBPDev_SlotID_EMPTY ||
    usbpdev_valid_slot_id(usbpdev_slot)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); (ret == TRUE ==>
    p_usbtd_slot_submit_usbtd_ret_global(va_get_globals(va_s0), va_get_globals(va_sM), td_slot)) &&
    (ret != TRUE ==> va_get_globals(va_sM) == va_get_globals(va_s0))
  ensures  var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    wimpdrv_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 9 * ARCH_WORD_BYTES); var input_param1:uint32 := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES); var input_param2:uint32 :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 7 * ARCH_WORD_BYTES); var
    input_param3:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 8 *
    ARCH_WORD_BYTES); var eehci_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)
    + 3 * ARCH_WORD_BYTES); ret == TRUE ==> (var td_type:word :=
    usbtd_map_get_type(va_get_globals(va_s0), td_slot);
    p_usbtd_slot_submit_modification_to_usbtd(va_get_globals(va_sM), td_slot, wimpdrv_slot_id,
    usbpdev_slot, input_param1, input_param2, input_param3, td_type, eehci_id))
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
  reveal_va_code__usbtd_slot_submit();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_ffi_usbtd_copy_from_user_stack_and_globals();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_Reg1ToReg6(va_b4, va_s4, va_sM);
  ghost var orig_ebp := va_get_reg(EBP, va_s9);
  ghost var orig_esp := va_get_reg(ESP, va_s9);
  ghost var orig_flags := va_get_sreg(EFLAGS, va_s9);
  assert IsAddrInStack(orig_esp - WK_STACK_FOR_EXTERNEL_FUNCS_SZ);  // line 776 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
  ghost var va_b14, va_s14 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var in_td_slot := va_get_reg(EBX, va_s14);
  ghost var va_b16, va_s16 := va_lemma_Load(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 6 * ARCH_WORD_BYTES);
  ghost var va_b17, va_s17 := va_lemma_PUSH(va_b16, va_s16, va_sM, va_op_word_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_Load(va_b17, va_s17, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES);
  ghost var va_b19, va_s19 := va_lemma_PUSH(va_b18, va_s18, va_sM, va_op_word_reg(EDI));
  ghost var va_b20, va_s20 := va_lemma_Load(va_b19, va_s19, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s20, va_sM, va_op_word_reg(EDI));
  ghost var va_b22, va_s22 := va_lemma_Load(va_b21, va_s21, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b23, va_s23 := va_lemma_PUSH(va_b22, va_s22, va_sM, va_op_word_reg(EDI));
  ghost var wimpdrv_slot_id := va_get_reg(EDI, va_s23);
  ghost var va_b25, va_s25 := va_lemma_PUSH(va_b23, va_s23, va_sM, va_op_word_reg(EBX));
  ghost var wk_mstate1 := va_s25.wk_mstate;
  ghost var va_b27, va_s27 := va_lemma_CALL_USBTD_Copy_From_User(va_b25, va_s25, va_sM);
  ghost var wk_mstate2 := va_s27.wk_mstate;
  ghost var regs2 := wk_mstate2.regs;
  ghost var stack2 := va_get_mem(va_s27);
  ghost var globals2 := va_get_globals(va_s27);
  ghost var va_b32, va_s32 := va_lemma_Load(va_b27, va_s27, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0);
  ghost var va_b33, va_s33 := va_lemma_POP_VOID(va_b32, va_s32, va_sM,
    FFI_USBTD_CopyFromUser_StackParamsWords * ARCH_WORD_BYTES);
  assert va_get_reg(ESP, va_s33) == orig_esp;  // line 800 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
  ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b33, va_s33, va_sM);
  ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
    va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s33, va_s35);
  if (va_cond_c35)
  {
    ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
    Lemma_ffi_usbtd_copy_from_user_DoNotModifyFlagsAndOtherUSBTDs(wk_mstate1, wk_mstate2, regs2,
      stack2, globals2);
    Lemma_usbtds_verifiedtds_do_not_associate_usbtd_HoldIfModifyingUSBTDRemainsInsecure(va_get_globals(va_old_s),
      globals2, in_td_slot);
    assert usbtds_verifiedtds_do_not_associate_usbtd(globals2, in_td_slot);  // line 806 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    assert ffi_preserve_sp_and_bp(wk_mstate1, regs2);  // line 808 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    Lemma_ffi_usbtd_copy_from_user_DoNotModifyOtherGlobalVariables(wk_mstate1, wk_mstate2, regs2,
      stack2, globals2);
    assert global_read_fullval(va_get_globals(va_old_s), G_EEHCI_MEM()) ==
      global_read_fullval(globals2, G_EEHCI_MEM());  // line 810 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    Lemma_eehci_mem_no_ref_to_usbtd_slot_Equivilant(va_get_globals(va_old_s), globals2, in_td_slot);
    assert eehci_mem_no_ref_to_usbtd_slot(globals2, in_td_slot);  // line 812 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    assert va_get_reg(ESP, va_s36) == orig_esp;  // line 813 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    Lemma_ffi_usbtd_copy_from_user_stack_and_globals_Properties(wk_mstate1, stack2, globals2);
    assert wimpdrv_valid_slot_id(wimpdrv_slot_id);  // line 816 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherUSBTDs(va_get_globals(va_old_s),
      globals2, in_td_slot);
    Lemma_ffi_usbtd_copy_from_user_copied_some_new_usbtd_PreserveOtherFieldsInUSBTDMem(va_get_globals(va_old_s),
      globals2, in_td_slot);
    ghost var va_b51, va_s51 := va_lemma_Load(va_b37, va_s36, va_s35, va_op_word_reg(EBX),
      va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
    ghost var va_b52, va_s52 := va_lemma_Load(va_b51, va_s51, va_s35, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
    ghost var va_b53, va_s53 := va_lemma_PUSH(va_b52, va_s52, va_s35, va_op_word_reg(EDI));
    ghost var va_b54, va_s54 := va_lemma_eechi_id_get_bus_id(va_b53, va_s53, va_s35);
    ghost var va_b55, va_s55 := va_lemma_Load(va_b54, va_s54, va_s35, va_op_word_reg(ESI),
      va_op_word_reg(ESP), 0);
    ghost var va_b56, va_s56 := va_lemma_POP_VOID(va_b55, va_s55, va_s35, 1 * ARCH_WORD_BYTES);
    assert va_get_reg(ESP, va_s56) == orig_esp;  // line 830 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    assert usbtds_verifiedtds_do_not_associate_usbtd(va_get_globals(va_s56), in_td_slot);  // line 831 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    ghost var va_b59, va_s59 := va_lemma_PUSH(va_b56, va_s56, va_s35, va_op_word_reg(ESI));
    ghost var va_b60, va_s60 := va_lemma_Load(va_b59, va_s59, va_s35, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 9 * ARCH_WORD_BYTES);
    ghost var va_b61, va_s61 := va_lemma_PUSH(va_b60, va_s60, va_s35, va_op_word_reg(EDI));
    ghost var va_b62, va_s62 := va_lemma_Load(va_b61, va_s61, va_s35, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 8 * ARCH_WORD_BYTES);
    ghost var va_b63, va_s63 := va_lemma_PUSH(va_b62, va_s62, va_s35, va_op_word_reg(EDI));
    ghost var va_b64, va_s64 := va_lemma_Load(va_b63, va_s63, va_s35, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 7 * ARCH_WORD_BYTES);
    ghost var va_b65, va_s65 := va_lemma_PUSH(va_b64, va_s64, va_s35, va_op_word_reg(EDI));
    ghost var va_b66, va_s66 := va_lemma_Load(va_b65, va_s65, va_s35, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 10 * ARCH_WORD_BYTES);
    ghost var va_b67, va_s67 := va_lemma_PUSH(va_b66, va_s66, va_s35, va_op_word_reg(EDI));
    ghost var va_b68, va_s68 := va_lemma_Load(va_b67, va_s67, va_s35, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
    ghost var va_b69, va_s69 := va_lemma_PUSH(va_b68, va_s68, va_s35, va_op_word_reg(EDI));
    assert va_get_reg(EDI, va_s69) == wimpdrv_slot_id;  // line 845 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    ghost var va_b71, va_s71 := va_lemma_PUSH(va_b69, va_s69, va_s35, va_op_word_reg(EBX));
    ghost var va_b72, va_s72 := va_lemma__usbtd_slot_submit_partial_otherfields(va_b71, va_s71,
      va_s35);
    ghost var va_b73, va_s73 := va_lemma_POP_VOID(va_b72, va_s72, va_s35, 7 * ARCH_WORD_BYTES);
    assert va_get_reg(ESP, va_s73) == orig_esp;  // line 849 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    ghost var globals3 := va_get_globals(va_s73);
    assert p_usbtd_slot_submit_usbtd_ret_global(globals2, globals3, in_td_slot);  // line 852 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    Lemma__usbtd_slot_submit_ProveProperty1(va_get_globals(va_old_s), globals2, globals3,
      in_td_slot);
    ghost var va_b78, va_s78 := va_lemma_Store(va_b73, va_s73, va_s35, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    va_s35 := va_lemma_empty(va_s78, va_s35);
  }
  else
  {
    ghost var va_b79 := va_get_block(va_get_ifFalse(va_c35));
    ghost var va_b80, va_s80 := va_lemma_Store(va_b79, va_s36, va_s35, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s35 := va_lemma_empty(va_s80, va_s35);
  }
  ghost var va_b81, va_s81 := va_lemma_POP_Reg1ToReg6(va_b35, va_s35, va_sM);
  ghost var va_b82, va_s82 := va_lemma_POP_OneReg(va_b81, va_s81, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s82, va_sM);
}
//--
predicate usbtd_slot_allocate_1slot_globals_relationship(
    old_globals:globalsmap, new_globals:globalsmap, new_td_slot:word, new_idword:word, new_td_type:word, new_pid:word, ret:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires ret == TRUE ==> usbtd_map_valid_slot_id(new_td_slot)
    requires (new_td_type == USBTDs_TYPE_QTD32) || (new_td_type == USBTDs_TYPE_QH32) || 
        (new_td_type == USBTDs_TYPE_iTD32) || (new_td_type == USBTDs_TYPE_siTD32)
{
    ((ret == TRUE) ==> (
            // Only one USB TD, and G_USBTD_ID_Counter is changed
        (forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != new_td_slot
            ==> p_usbtd_equal(old_globals, new_globals, i)
        ) &&
        globals_other_gvar_unchanged_2vars(old_globals, new_globals, G_USBTD_MAP_MEM(), G_USBTD_ID_Counter()) &&
            // The USB TD is changed as expected
        usbtd_has_clear_content(new_globals, new_td_slot, new_td_type) &&
        usbtd_map_get_pid(new_globals, new_td_slot) == WS_PartitionID(new_pid) &&
        usbtd_map_get_type(new_globals, new_td_slot) == new_td_type &&
        usbtd_map_get_flags(new_globals, new_td_slot) == 0 &&
        usbtd_map_get_idword(new_globals, new_td_slot) == new_idword
    )) &&
    ((ret != TRUE) ==> globals_other_gvar_unchanged(old_globals, new_globals, G_USBTD_ID_Counter()))
}

predicate usbtd_slot_deallocate_1slot_globals_relationship(old_globals:globalsmap, new_globals:globalsmap, td_slot:word, ret:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires ret == TRUE ==> usbtd_map_valid_slot_id(td_slot)
{
    ((ret == TRUE) ==> (
            // Only one USB TD is changed
        usbtd_map_modify_one_usbtd_only(old_globals, new_globals, td_slot) &&
            // The USB TD is changed as expected
        p_usbtd_content_equal(old_globals, new_globals, td_slot) &&
        usbtd_map_get_pid(new_globals, td_slot) == WS_PartitionID(PID_INVALID) &&
        usbtd_map_get_flags(new_globals, td_slot) == 0
    )) &&
    ((ret != TRUE) ==> global_non_scratchpad_vars_are_unchanged(old_globals, new_globals))
}

predicate p_usbtd_slot_allocate_1slot_private_globals_relationship(
    old_globals:globalsmap, new_globals:globalsmap, new_td_slot:word, new_usbtd_idword:word, new_td_type:word, new_pid:word, ret:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires ret == TRUE ==> usbtd_map_valid_slot_id(new_td_slot)
    requires (new_td_type == USBTDs_TYPE_QTD32) || (new_td_type == USBTDs_TYPE_QH32) || 
        (new_td_type == USBTDs_TYPE_iTD32) || (new_td_type == USBTDs_TYPE_siTD32)
{
    ((ret == TRUE) ==> (
            // Only one USB TD is changed
        usbtd_map_modify_one_usbtd_only(old_globals, new_globals, new_td_slot) &&
            // The USB TD is changed as expected
        usbtd_has_clear_content(new_globals, new_td_slot, new_td_type) &&
        usbtd_map_get_pid(new_globals, new_td_slot) == WS_PartitionID(new_pid) &&
        usbtd_map_get_idword(new_globals, new_td_slot) == new_usbtd_idword &&
        usbtd_map_get_type(new_globals, new_td_slot) == new_td_type &&
        usbtd_map_get_flags(new_globals, new_td_slot) == 0
    )) &&
    ((ret != TRUE) ==> new_globals == old_globals)
}

lemma Lemma_usbtd_slot_allocate_1slot_ProveProperty2(
    old_globals:globalsmap, globals1:globalsmap, globals2:globalsmap, 
    td_slot:word, new_id:word, new_td_type:word, new_pid:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(td_slot)
    requires (new_td_type == USBTDs_TYPE_QTD32) || (new_td_type == USBTDs_TYPE_QH32) || 
        (new_td_type == USBTDs_TYPE_iTD32) || (new_td_type == USBTDs_TYPE_siTD32)

    requires globals_other_gvar_unchanged(old_globals, globals1, G_USBTD_ID_Counter())
    requires p_usbtd_slot_allocate_1slot_private_globals_relationship(globals1, globals2, td_slot, new_id, new_td_type, new_pid, TRUE)

    ensures usbtd_slot_allocate_1slot_globals_relationship(old_globals, globals2, td_slot, new_id, new_td_type, new_pid, TRUE)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    reveal ffi_usbtd_clear_content_stack_and_globals_qtd32();
    reveal ffi_usbtd_clear_content_stack_and_globals_qh32();

    forall i:uint32 | usbtd_map_valid_slot_id(i) && i != td_slot
        ensures p_usbtd_equal(old_globals, globals2, i)
    {
        assert p_usbtd_equal(old_globals, globals1, i);

        Lemma_p_usbtd_equal_transitive(old_globals, globals1, globals2, i);
        //Lemma_p_usbtd_equal_transitive(old_globals, globals2, new_globals, i);
    } 
}

// Prove the property 1 of <_usbtd_slot_submit>
lemma Lemma__usbtd_slot_submit_ProveProperty1(old_globals:globalsmap, globals2:globalsmap, new_globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbtd_map_valid_slot_id(slot)

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_idword(old_globals, i) == usbtd_map_get_idword(globals2, i)
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_pid(old_globals, i) == usbtd_map_get_pid(globals2, i)
    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != slot
        ==> p_usbtd_equal(old_globals, globals2, i)

    requires globals_other_gvar_unchanged(old_globals, globals2, G_USBTD_MAP_MEM())

    requires p_usbtd_slot_submit_usbtd_ret_global(globals2, new_globals, slot)

    ensures p_usbtd_slot_submit_usbtd_ret_global(old_globals, new_globals, slot)
{
    forall i:uint32 | usbtd_map_valid_slot_id(i) && i != slot
        ensures p_usbtd_equal(old_globals, new_globals, i)
    {
        Lemma_p_usbtd_equal_transitive(old_globals, globals2, new_globals, i);
    }
}

// Lemma: In a sane state, if a USB TD is inactive, then no verified/secure USB TD refs the USB TD
lemma Lemma_InstSaneState_IfUSBTDIsInactive_Then_usbtds_verifiedtds_do_not_associate_usbtd(globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidGlobalVars_Vals(globals)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(globals)

    requires usbtd_map_valid_slot_id(td_slot)
    requires usbtd_map_get_pid(globals, td_slot) == WS_PartitionID(PID_INVALID)

    ensures usbtds_verifiedtds_do_not_associate_usbtd(globals, td_slot)
{
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();

    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    reveal usbtds_verifiedtds_do_not_associate_usbtd_qtd32();
    reveal usbtds_verifiedtds_do_not_associate_usbtd_qh32();
}

// Lemma: In a sane state, if <usbtd_find_referencing_secure_slot> returns false, then <usbtds_verifiedtds_do_not_associate_usbtd> is true
lemma Lemma_InstSaneState_usbtd_find_referencing_secure_slot_ReturnFalseImplies_usbtds_verifiedtds_do_not_associate_usbtd(
    globals:globalsmap, target_td_slot:uint32
)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidGlobalVars_Vals(globals)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(globals)

    requires forall i:uint32 :: usbtd_map_valid_slot_id(i)
            ==> !(usbtd_is_slot_ref_target_slot(globals, i, target_td_slot) &&
                TestBit(usbtd_map_get_flags(globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit))

    requires usbtd_map_valid_slot_id(target_td_slot)
    ensures usbtds_verifiedtds_do_not_associate_usbtd(globals, target_td_slot)
{
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();

    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    reveal usbtds_verifiedtds_do_not_associate_usbtd_qtd32();
    reveal usbtds_verifiedtds_do_not_associate_usbtd_qh32();
}

// Lemma: If <global_non_scratchpad_vars_are_unchanged>, then the new global variables always satisfy 
// usbtds_verifiedtds_do_not_associate_usbtd
lemma Lemma_usbtds_verifiedtds_do_not_associate_usbtd_HoldIfNonScratchpadGVarsAreUnmodified(globals1:globalsmap, globals2:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires global_non_scratchpad_vars_are_unchanged(globals1, globals2)

    requires usbtds_verifiedtds_do_not_associate_usbtd(globals1, slot)

    ensures usbtds_verifiedtds_do_not_associate_usbtd(globals2, slot)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();
    reveal usbtds_verifiedtds_do_not_associate_usbtd_qtd32();
    reveal usbtds_verifiedtds_do_not_associate_usbtd_qh32();
    reveal global_non_scratchpad_vars_are_unchanged();
}

lemma Lemma_usbtd_slot_allocate_1slot_private_ProvePreConditionsOfUSBTDSetID(globals:globalsmap, slot:word, usbtd_idword:word)
    requires WK_ValidGlobalVars_Decls(globals)

    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) &&
                usbtd_map_get_idword(globals, i) != USBTD_ID_INVALID
            ==> usbtd_map_get_idword(globals, i) != usbtd_idword

    ensures forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != slot &&
                usbtd_map_get_idword(globals, i) != USBTD_ID_INVALID
            ==> usbtd_map_get_idword(globals, i) != usbtd_idword
{
    // Dafny can automatically prove this lemma
}
