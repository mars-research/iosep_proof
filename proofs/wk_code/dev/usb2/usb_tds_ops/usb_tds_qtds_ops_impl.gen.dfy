include "usb_tds_ops_impl.gen.dfy"
include "usb_tds_checks_qtd.gen.dfy"
include "usb_tds_ops.i.dfy"
include "..\\..\\..\\mm\\wk_mem.i.dfy"
include "usb_tds_qtds_ops.dafny21.gen.dfy"
//-- _usbtd_slot_submit_and_verify_qtd32_private
//--
//-- USBTD_slot_submit_and_verify_qtd32_basicchecks
//--
//-- USBTD_slot_submit_and_verify_qtd32_Impl

function method{:opaque} va_code_USBTD_slot_submit_and_verify_qtd32_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EAX)), va_CCons(va_code_Load(va_op_word_reg(EAX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code__usbtd_slot_submit_and_verify_morechecks(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_POP_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_USBTD_slot_submit_and_verify_qtd32_basicchecks(), va_CNil())))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))), va_CNil()))))))))))))
}

lemma{:timeLimitMultiplier 3} va_lemma_USBTD_slot_submit_and_verify_qtd32_Impl(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_USBTD_slot_submit_and_verify_qtd32_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 53 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES
    + 8 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := 8 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1
    * ARCH_WORD_BYTES); var input_param1:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 5 * ARCH_WORD_BYTES); var input_param2:uint32 := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES); var input_param3:uint32 :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 7 * ARCH_WORD_BYTES); var
    eehci_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 3 *
    ARCH_WORD_BYTES); var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); (((((((ret
    == TRUE ==> usbtd_map_valid_slot_id(td_slot)) && (ret == TRUE ==>
    wimpdrv_valid_slot_id(wimpdrv_slot_id))) && (ret == TRUE ==>
    p_usbtd_slot_submit_and_verify_usbtd_ret_global(va_get_globals(va_s0), va_get_globals(va_sM),
    td_slot))) && (ret == TRUE ==> wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot_id) in
    pids_parse_g_wimp_pids(va_get_globals(va_s0)))) && (ret == TRUE ==>
    wimpdrv_get_pid(va_get_globals(va_s0), wimpdrv_slot_id) ==
    usbtd_map_get_pid(va_get_globals(va_s0), td_slot))) && (ret == TRUE ==>
    usbtd_map_get_type(va_get_globals(va_sM), td_slot) == USBTDs_TYPE_QTD32 &&
    usbtd_map_get_flags(va_get_globals(va_sM), td_slot) == SetBit(SetBit(0,
    USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit))) && (ret == TRUE ==>
    p_usbtd_slot_submit_modification_to_usbtd(va_get_globals(va_sM), td_slot, wimpdrv_slot_id,
    WimpUSBPDev_SlotID_EMPTY, input_param1, input_param2, input_param3, USBTDs_TYPE_QTD32,
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
  reveal_va_code_USBTD_slot_submit_and_verify_qtd32_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b5, va_s5 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EAX));
  ghost var va_b6, va_s6 := va_lemma_Load(va_b5, va_s5, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b7, va_s7 := va_lemma_PUSH(va_b6, va_s6, va_sM, va_op_word_reg(EAX));
  ghost var va_b8, va_s8 := va_lemma_Load(va_b7, va_s7, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b9, va_s9 := va_lemma_PUSH(va_b8, va_s8, va_sM, va_op_word_reg(EAX));
  ghost var va_b10, va_s10 := va_lemma__usbtd_slot_submit_and_verify_morechecks(va_b9, va_s9,
    va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0);
  ghost var va_b12, va_s12 := va_lemma_POP_VOID(va_b11, va_s11, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s13, va_c13, va_b13 := va_lemma_block(va_b12, va_s12, va_sM);
  ghost var va_cond_c13, va_s14:va_state := va_lemma_ifElse(va_get_ifCond(va_c13),
    va_get_ifTrue(va_c13), va_get_ifFalse(va_c13), va_s12, va_s13);
  if (va_cond_c13)
  {
    ghost var va_b15 := va_get_block(va_get_ifTrue(va_c13));
    ghost var va_b16, va_s16 := va_lemma_POP_OneReg(va_b15, va_s14, va_s13, va_op_reg_reg(EAX));
    ghost var va_b17, va_s17 := va_lemma_POP_OneReg(va_b16, va_s16, va_s13, va_op_reg_reg(EBP));
    ghost var va_b18, va_s18 := va_lemma_USBTD_slot_submit_and_verify_qtd32_basicchecks(va_b17,
      va_s17, va_s13);
    va_s13 := va_lemma_empty(va_s18, va_s13);
  }
  else
  {
    ghost var va_b19 := va_get_block(va_get_ifFalse(va_c13));
    reveal_global_non_scratchpad_vars_are_unchanged();
    ghost var va_b21, va_s21 := va_lemma_Store(va_b19, va_s14, va_s13, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b22, va_s22 := va_lemma_POP_OneReg(va_b21, va_s21, va_s13, va_op_reg_reg(EAX));
    ghost var va_b23, va_s23 := va_lemma_POP_OneReg(va_b22, va_s22, va_s13, va_op_reg_reg(EBP));
    va_s13 := va_lemma_empty(va_s23, va_s13);
  }
  va_sM := va_lemma_empty(va_s13, va_sM);
}
//--
//-- USBTD_slot_submit_and_verify_qtd32_basicchecks

function method{:opaque} va_code_USBTD_slot_submit_and_verify_qtd32_basicchecks():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_usbtd_check_td_slot_id(va_op_reg_reg(ESI), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(ESI)),
    va_CCons(va_code__usbtd_find_referencing_secure_slot(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 8 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 7 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 6 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code__usbtd_slot_submit_and_verify_qtd32_private(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(8
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil()))))))))))))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))
}

lemma{:timeLimitMultiplier 30}
  va_lemma_USBTD_slot_submit_and_verify_qtd32_basicchecks(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_USBTD_slot_submit_and_verify_qtd32_basicchecks(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 53 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES
    + 8 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := 8 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1
    * ARCH_WORD_BYTES); var input_param1:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 5 * ARCH_WORD_BYTES); var input_param2:uint32 := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES); var input_param3:uint32 :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 7 * ARCH_WORD_BYTES); var
    eehci_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 3 *
    ARCH_WORD_BYTES); var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((((ret ==
    TRUE ==> usbtd_map_valid_slot_id(td_slot)) && (ret == TRUE ==>
    p_usbtd_slot_submit_and_verify_usbtd_ret_global(va_get_globals(va_s0), va_get_globals(va_sM),
    td_slot))) && (ret == TRUE ==> usbtd_map_get_type(va_get_globals(va_sM), td_slot) ==
    USBTDs_TYPE_QTD32 && usbtd_map_get_flags(va_get_globals(va_sM), td_slot) == SetBit(SetBit(0,
    USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit))) && (ret == TRUE ==>
    p_usbtd_slot_submit_modification_to_usbtd(va_get_globals(va_sM), td_slot, wimpdrv_slot_id,
    WimpUSBPDev_SlotID_EMPTY, input_param1, input_param2, input_param3, USBTDs_TYPE_QTD32,
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
  reveal_va_code_USBTD_slot_submit_and_verify_qtd32_basicchecks();
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
  ghost var orig_mem := va_get_mem(va_s7);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b7, va_s7, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_usbtd_check_td_slot_id(va_b11, va_s11, va_sM,
    va_op_reg_reg(ESI), va_op_reg_reg(EAX));
  ghost var va_s13, va_c13, va_b13 := va_lemma_block(va_b12, va_s12, va_sM);
  ghost var va_cond_c13, va_s14:va_state := va_lemma_ifElse(va_get_ifCond(va_c13),
    va_get_ifTrue(va_c13), va_get_ifFalse(va_c13), va_s12, va_s13);
  if (va_cond_c13)
  {
    ghost var va_b15 := va_get_block(va_get_ifTrue(va_c13));
    ghost var va_b16, va_s16 := va_lemma_PUSH_VOID(va_b15, va_s14, va_s13, 1 * ARCH_WORD_BYTES);
    ghost var va_b17, va_s17 := va_lemma_PUSH(va_b16, va_s16, va_s13, va_op_word_reg(ESI));
    ghost var va_b18, va_s18 := va_lemma__usbtd_find_referencing_secure_slot(va_b17, va_s17,
      va_s13);
    ghost var va_b19, va_s19 := va_lemma_Load(va_b18, va_s18, va_s13, va_op_word_reg(EAX),
      va_op_word_reg(ESP), 0);
    lemma_MulModZero(2, ARCH_WORD_BYTES);
    ghost var va_b21, va_s21 := va_lemma_POP_VOID(va_b19, va_s19, va_s13, 2 * ARCH_WORD_BYTES);
    assert va_get_reg(ESP, va_s21) == orig_esp;  // line 220 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
    assert va_get_reg(EBP, va_s21) == orig_ebp;  // line 221 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
    assert stack_under_sp_is_unchanged(orig_mem, va_get_mem(va_s21), va_get_reg(ESP, va_s21));  // line 222 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
    ghost var va_s25, va_c25, va_b25 := va_lemma_block(va_b21, va_s21, va_s13);
    ghost var va_cond_c25, va_s26:va_state := va_lemma_ifElse(va_get_ifCond(va_c25),
      va_get_ifTrue(va_c25), va_get_ifFalse(va_c25), va_s21, va_s25);
    if (va_cond_c25)
    {
      ghost var va_b27 := va_get_block(va_get_ifTrue(va_c25));
      Lemma_InstSaneState_usbtd_find_referencing_secure_slot_ReturnFalseImplies_usbtds_verifiedtds_do_not_associate_usbtd(va_get_globals(va_s26),
        va_get_reg(ESI, va_s26));
      ghost var va_b29, va_s29 := va_lemma_Load(va_b27, va_s26, va_s25, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 8 * ARCH_WORD_BYTES);
      ghost var va_b30, va_s30 := va_lemma_PUSH(va_b29, va_s29, va_s25, va_op_word_reg(EDI));
      ghost var va_b31, va_s31 := va_lemma_Load(va_b30, va_s30, va_s25, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 7 * ARCH_WORD_BYTES);
      ghost var va_b32, va_s32 := va_lemma_PUSH(va_b31, va_s31, va_s25, va_op_word_reg(EDI));
      ghost var va_b33, va_s33 := va_lemma_Load(va_b32, va_s32, va_s25, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 6 * ARCH_WORD_BYTES);
      ghost var va_b34, va_s34 := va_lemma_PUSH(va_b33, va_s33, va_s25, va_op_word_reg(EDI));
      ghost var va_b35, va_s35 := va_lemma_Load(va_b34, va_s34, va_s25, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES);
      ghost var va_b36, va_s36 := va_lemma_PUSH(va_b35, va_s35, va_s25, va_op_word_reg(EDI));
      ghost var va_b37, va_s37 := va_lemma_Load(va_b36, va_s36, va_s25, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
      ghost var va_b38, va_s38 := va_lemma_PUSH(va_b37, va_s37, va_s25, va_op_word_reg(EDI));
      ghost var va_b39, va_s39 := va_lemma_Load(va_b38, va_s38, va_s25, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
      ghost var va_b40, va_s40 := va_lemma_PUSH(va_b39, va_s39, va_s25, va_op_word_reg(EDI));
      ghost var va_b41, va_s41 := va_lemma_Load(va_b40, va_s40, va_s25, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
      ghost var va_b42, va_s42 := va_lemma_PUSH(va_b41, va_s41, va_s25, va_op_word_reg(EDI));
      ghost var va_b43, va_s43 := va_lemma_Load(va_b42, va_s42, va_s25, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
      ghost var va_b44, va_s44 := va_lemma_PUSH(va_b43, va_s43, va_s25, va_op_word_reg(EDI));
      ghost var va_b45, va_s45 := va_lemma__usbtd_slot_submit_and_verify_qtd32_private(va_b44,
        va_s44, va_s25);
      ghost var va_b46, va_s46 := va_lemma_Load(va_b45, va_s45, va_s25, va_op_word_reg(EDI),
        va_op_word_reg(ESP), 0);
      ghost var va_b47, va_s47 := va_lemma_POP_VOID(va_b46, va_s46, va_s25, 8 * ARCH_WORD_BYTES);
      ghost var va_s48, va_c48, va_b48 := va_lemma_block(va_b47, va_s47, va_s25);
      ghost var va_cond_c48, va_s49:va_state := va_lemma_ifElse(va_get_ifCond(va_c48),
        va_get_ifTrue(va_c48), va_get_ifFalse(va_c48), va_s47, va_s48);
      if (va_cond_c48)
      {
        ghost var va_b50 := va_get_block(va_get_ifTrue(va_c48));
        ghost var va_b51, va_s51 := va_lemma_Store(va_b50, va_s49, va_s48, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(TRUE));
        va_s48 := va_lemma_empty(va_s51, va_s48);
      }
      else
      {
        ghost var va_b52 := va_get_block(va_get_ifFalse(va_c48));
        ghost var va_b53, va_s53 := va_lemma_Store(va_b52, va_s49, va_s48, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        va_s48 := va_lemma_empty(va_s53, va_s48);
      }
      va_s25 := va_lemma_empty(va_s48, va_s25);
    }
    else
    {
      ghost var va_b54 := va_get_block(va_get_ifFalse(va_c25));
      ghost var va_b55, va_s55 := va_lemma_Store(va_b54, va_s26, va_s25, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s55) == va_get_globals(va_old_s);  // line 261 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s55));
      assert global_non_scratchpad_vars_are_unchanged(va_get_globals(va_old_s),
        va_get_globals(va_s55));  // line 263 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
      va_s25 := va_lemma_empty(va_s55, va_s25);
    }
    va_s13 := va_lemma_empty(va_s25, va_s13);
  }
  else
  {
    ghost var va_b59 := va_get_block(va_get_ifFalse(va_c13));
    ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s14, va_s13, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s60) == va_get_globals(va_old_s);  // line 270 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s60));
    assert global_non_scratchpad_vars_are_unchanged(va_get_globals(va_old_s),
      va_get_globals(va_s60));  // line 272 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
    va_s13 := va_lemma_empty(va_s60, va_s13);
  }
  ghost var va_b64, va_s64 := va_lemma_POP_Reg1ToReg6(va_b13, va_s13, va_sM);
  ghost var va_b65, va_s65 := va_lemma_POP_OneReg(va_b64, va_s64, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s65, va_sM);
}
//--
//-- _usbtd_slot_submit_and_verify_qtd32_private

function method{:opaque} va_code__usbtd_slot_submit_and_verify_qtd32_private():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(ESI)),
    va_CCons(va_code_CALL_EEHCI_FIND_RefToUSBTD(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_const_cmp(eEHCI_SlotID_EMPTY)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(ESI)), va_CCons(va_code_usbtd_get_flags(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_const_cmp(0)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(ESI)), va_CCons(va_code_usbtd_get_type(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI),
    va_const_cmp(USBTDs_TYPE_QTD32)),
    va_Block(va_CCons(va_code_PUSH(va_const_word(WimpUSBPDev_SlotID_EMPTY)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 8 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 7 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 6 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code__usbtd_slot_submit_and_verify_qtd32_inner(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(9
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil())))))))))))))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))
}

lemma{:timeLimitMultiplier 100}
  va_lemma__usbtd_slot_submit_and_verify_qtd32_private(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbtd_slot_submit_and_verify_qtd32_private(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 37 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES
    + 9 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := 8 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(td_slot) &&
    usbtds_verifiedtds_do_not_associate_usbtd(va_get_globals(va_s0), td_slot)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var wimpdrv_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1
    * ARCH_WORD_BYTES); var input_param1:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 5 * ARCH_WORD_BYTES); var input_param2:uint32 := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 6 * ARCH_WORD_BYTES); var input_param3:uint32 :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 7 * ARCH_WORD_BYTES); var
    eehci_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 3 *
    ARCH_WORD_BYTES); var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((((ret ==
    TRUE ==> usbtd_map_valid_slot_id(td_slot)) && (ret == TRUE ==>
    p_usbtd_slot_submit_and_verify_usbtd_ret_global(va_get_globals(va_s0), va_get_globals(va_sM),
    td_slot))) && (ret == TRUE ==> usbtd_map_get_type(va_get_globals(va_sM), td_slot) ==
    USBTDs_TYPE_QTD32 && usbtd_map_get_flags(va_get_globals(va_sM), td_slot) == SetBit(SetBit(0,
    USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit))) && (ret == TRUE ==>
    p_usbtd_slot_submit_modification_to_usbtd(va_get_globals(va_sM), td_slot, wimpdrv_slot_id,
    WimpUSBPDev_SlotID_EMPTY, input_param1, input_param2, input_param3, USBTDs_TYPE_QTD32,
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
  reveal_va_code__usbtd_slot_submit_and_verify_qtd32_private();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  Lemma_IsAddrInStack_ProveEveryAddrInRangeIsValidAddrInStack(va_get_reg(EBP, va_s3) + 8 *
    ARCH_WORD_BYTES, va_get_reg(EBP, va_s3) - 42 * ARCH_WORD_BYTES);
  ghost var va_b8, va_s8 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var orig_esp := va_get_reg(ESP, va_s8);
  ghost var orig_ebp := va_get_reg(EBP, va_s8);
  ghost var orig_mem := va_get_mem(va_s8);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b8, va_s8, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_PUSH(va_b12, va_s12, va_sM, va_op_word_reg(ESI));
  ghost var old_wkm := va_s13.wk_mstate;
  ghost var va_b15, va_s15 := va_lemma_CALL_EEHCI_FIND_RefToUSBTD(va_b13, va_s13, va_sM);
  ghost var new_stack1 := va_get_mem(va_s15);
  ghost var va_b17, va_s17 := va_lemma_Load(va_b15, va_s15, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0);
  lemma_MulModZero(1, ARCH_WORD_BYTES);
  ghost var va_b19, va_s19 := va_lemma_POP_VOID(va_b17, va_s17, va_sM, 1 * ARCH_WORD_BYTES);
  assert va_get_reg(ESP, va_s19) == orig_esp;  // line 382 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
  assert va_get_reg(EBP, va_s19) == orig_ebp;  // line 383 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
  assert stack_under_sp_is_unchanged(orig_mem, va_get_mem(va_s19), va_get_reg(ESP, va_s19));  // line 384 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
  ghost var va_b23, va_s23 := va_lemma_Load(va_b19, va_s19, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_s24, va_c24, va_b24 := va_lemma_block(va_b23, va_s23, va_sM);
  ghost var va_cond_c24, va_s25:va_state := va_lemma_ifElse(va_get_ifCond(va_c24),
    va_get_ifTrue(va_c24), va_get_ifFalse(va_c24), va_s23, va_s24);
  if (va_cond_c24)
  {
    ghost var va_b26 := va_get_block(va_get_ifTrue(va_c24));
    Lemma_eehci_find_ref_to_usbtd_property(old_wkm, new_stack1);
    assert forall i:uint32 :: eehci_valid_slot_id(i) ==>
      EECHI_DoNotRefGivenUSBTD(va_get_globals(va_s25), i, va_get_reg(ESI, va_s25));  // line 390 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
    assert eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_s25), va_get_reg(ESI, va_s25));  // line 392 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
    ghost var va_b30, va_s30 := va_lemma_PUSH(va_b26, va_s25, va_s24, va_op_word_reg(ESI));
    ghost var va_b31, va_s31 := va_lemma_usbtd_get_flags(va_b30, va_s30, va_s24);
    ghost var va_b32, va_s32 := va_lemma_Load(va_b31, va_s31, va_s24, va_op_word_reg(EDI),
      va_op_word_reg(ESP), 0);
    lemma_MulModZero(1, ARCH_WORD_BYTES);
    ghost var va_b34, va_s34 := va_lemma_POP_VOID(va_b32, va_s32, va_s24, 1 * ARCH_WORD_BYTES);
    assert va_get_reg(ESP, va_s34) == orig_esp;  // line 400 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
    assert va_get_reg(EBP, va_s34) == orig_ebp;  // line 401 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
    ghost var va_s37, va_c37, va_b37 := va_lemma_block(va_b34, va_s34, va_s24);
    ghost var va_cond_c37, va_s38:va_state := va_lemma_ifElse(va_get_ifCond(va_c37),
      va_get_ifTrue(va_c37), va_get_ifFalse(va_c37), va_s34, va_s37);
    if (va_cond_c37)
    {
      ghost var va_b39 := va_get_block(va_get_ifTrue(va_c37));
      ghost var va_b40, va_s40 := va_lemma_PUSH(va_b39, va_s38, va_s37, va_op_word_reg(ESI));
      ghost var va_b41, va_s41 := va_lemma_usbtd_get_type(va_b40, va_s40, va_s37);
      ghost var va_b42, va_s42 := va_lemma_Load(va_b41, va_s41, va_s37, va_op_word_reg(EDI),
        va_op_word_reg(ESP), 0);
      lemma_MulModZero(1, ARCH_WORD_BYTES);
      ghost var va_b44, va_s44 := va_lemma_POP_VOID(va_b42, va_s42, va_s37, 1 * ARCH_WORD_BYTES);
      assert va_get_reg(ESP, va_s44) == orig_esp;  // line 411 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
      assert va_get_reg(EBP, va_s44) == orig_ebp;  // line 412 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
      ghost var va_s47, va_c47, va_b47 := va_lemma_block(va_b44, va_s44, va_s37);
      ghost var va_cond_c47, va_s48:va_state := va_lemma_ifElse(va_get_ifCond(va_c47),
        va_get_ifTrue(va_c47), va_get_ifFalse(va_c47), va_s44, va_s47);
      if (va_cond_c47)
      {
        ghost var va_b49 := va_get_block(va_get_ifTrue(va_c47));
        ghost var va_b50, va_s50 := va_lemma_PUSH(va_b49, va_s48, va_s47,
          va_const_word(WimpUSBPDev_SlotID_EMPTY));
        ghost var va_b51, va_s51 := va_lemma_Load(va_b50, va_s50, va_s47, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 8 * ARCH_WORD_BYTES);
        ghost var va_b52, va_s52 := va_lemma_PUSH(va_b51, va_s51, va_s47, va_op_word_reg(EDI));
        assert va_get_reg(ESP, va_s52) == orig_esp - 2 * ARCH_WORD_BYTES;  // line 420 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        assert va_get_reg(EBP, va_s52) == orig_ebp;  // line 421 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        ghost var va_b55, va_s55 := va_lemma_Load(va_b52, va_s52, va_s47, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 7 * ARCH_WORD_BYTES);
        ghost var va_b56, va_s56 := va_lemma_PUSH(va_b55, va_s55, va_s47, va_op_word_reg(EDI));
        assert va_get_reg(ESP, va_s56) == orig_esp - 3 * ARCH_WORD_BYTES;  // line 424 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        assert va_get_reg(EBP, va_s56) == orig_ebp;  // line 425 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        ghost var va_b59, va_s59 := va_lemma_Load(va_b56, va_s56, va_s47, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 6 * ARCH_WORD_BYTES);
        ghost var va_b60, va_s60 := va_lemma_PUSH(va_b59, va_s59, va_s47, va_op_word_reg(EDI));
        assert va_get_reg(ESP, va_s60) == orig_esp - 4 * ARCH_WORD_BYTES;  // line 428 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        assert va_get_reg(EBP, va_s60) == orig_ebp;  // line 429 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        ghost var va_b63, va_s63 := va_lemma_Load(va_b60, va_s60, va_s47, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES);
        ghost var va_b64, va_s64 := va_lemma_PUSH(va_b63, va_s63, va_s47, va_op_word_reg(EDI));
        assert va_get_reg(ESP, va_s64) == orig_esp - 5 * ARCH_WORD_BYTES;  // line 432 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        assert va_get_reg(EBP, va_s64) == orig_ebp;  // line 433 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        ghost var va_b67, va_s67 := va_lemma_Load(va_b64, va_s64, va_s47, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
        ghost var va_b68, va_s68 := va_lemma_PUSH(va_b67, va_s67, va_s47, va_op_word_reg(EDI));
        assert va_get_reg(ESP, va_s68) == orig_esp - 6 * ARCH_WORD_BYTES;  // line 436 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        assert va_get_reg(EBP, va_s68) == orig_ebp;  // line 437 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        ghost var va_b71, va_s71 := va_lemma_Load(va_b68, va_s68, va_s47, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
        ghost var va_b72, va_s72 := va_lemma_PUSH(va_b71, va_s71, va_s47, va_op_word_reg(EDI));
        assert va_get_reg(ESP, va_s72) == orig_esp - 7 * ARCH_WORD_BYTES;  // line 440 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        assert va_get_reg(EBP, va_s72) == orig_ebp;  // line 441 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        ghost var va_b75, va_s75 := va_lemma_Load(va_b72, va_s72, va_s47, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
        ghost var va_b76, va_s76 := va_lemma_PUSH(va_b75, va_s75, va_s47, va_op_word_reg(EDI));
        assert va_get_reg(ESP, va_s76) == orig_esp - 8 * ARCH_WORD_BYTES;  // line 444 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        assert va_get_reg(EBP, va_s76) == orig_ebp;  // line 445 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        ghost var va_b79, va_s79 := va_lemma_Load(va_b76, va_s76, va_s47, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
        ghost var va_b80, va_s80 := va_lemma_PUSH(va_b79, va_s79, va_s47, va_op_word_reg(EDI));
        ghost var va_b81, va_s81 := va_lemma__usbtd_slot_submit_and_verify_qtd32_inner(va_b80,
          va_s80, va_s47);
        ghost var va_b82, va_s82 := va_lemma_Load(va_b81, va_s81, va_s47, va_op_word_reg(EDI),
          va_op_word_reg(ESP), 0);
        lemma_MulModZero(9, ARCH_WORD_BYTES);
        ghost var va_b84, va_s84 := va_lemma_POP_VOID(va_b82, va_s82, va_s47, 9 * ARCH_WORD_BYTES);
        assert va_get_reg(ESP, va_s84) == orig_esp;  // line 452 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        assert va_get_reg(EBP, va_s84) == orig_ebp;  // line 453 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        assert stack_under_sp_is_unchanged(orig_mem, va_get_mem(va_s84), va_get_reg(ESP, va_s84)); 
          // line 454 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        ghost var va_s88, va_c88, va_b88 := va_lemma_block(va_b84, va_s84, va_s47);
        ghost var va_cond_c88, va_s89:va_state := va_lemma_ifElse(va_get_ifCond(va_c88),
          va_get_ifTrue(va_c88), va_get_ifFalse(va_c88), va_s84, va_s88);
        if (va_cond_c88)
        {
          ghost var va_b90 := va_get_block(va_get_ifTrue(va_c88));
          ghost var va_b91, va_s91 := va_lemma_Store(va_b90, va_s89, va_s88, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          assert p_usbtd_slot_submit_and_verify_usbtd_ret_global(va_get_globals(va_old_s),
            va_get_globals(va_s91), va_get_reg(ESI, va_s91));  // line 459 column 21 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
          va_s88 := va_lemma_empty(va_s91, va_s88);
        }
        else
        {
          ghost var va_b93 := va_get_block(va_get_ifFalse(va_c88));
          ghost var va_b94, va_s94 := va_lemma_Store(va_b93, va_s89, va_s88, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert global_non_scratchpad_vars_are_unchanged(va_get_globals(va_old_s),
            va_get_globals(va_s94));  // line 464 column 21 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
          va_s88 := va_lemma_empty(va_s94, va_s88);
        }
        va_s47 := va_lemma_empty(va_s88, va_s47);
      }
      else
      {
        ghost var va_b96 := va_get_block(va_get_ifFalse(va_c47));
        ghost var va_b97, va_s97 := va_lemma_Store(va_b96, va_s48, va_s47, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s97) == va_get_globals(va_old_s);  // line 471 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s97));
        assert global_non_scratchpad_vars_are_unchanged(va_get_globals(va_old_s),
          va_get_globals(va_s97));  // line 473 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
        va_s47 := va_lemma_empty(va_s97, va_s47);
      }
      va_s37 := va_lemma_empty(va_s47, va_s37);
    }
    else
    {
      ghost var va_b101 := va_get_block(va_get_ifFalse(va_c37));
      ghost var va_b102, va_s102 := va_lemma_Store(va_b101, va_s38, va_s37, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s102) == va_get_globals(va_old_s);  // line 480 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s102));
      assert global_non_scratchpad_vars_are_unchanged(va_get_globals(va_old_s),
        va_get_globals(va_s102));  // line 482 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
      va_s37 := va_lemma_empty(va_s102, va_s37);
    }
    va_s24 := va_lemma_empty(va_s37, va_s24);
  }
  else
  {
    ghost var va_b106 := va_get_block(va_get_ifFalse(va_c24));
    ghost var va_b107, va_s107 := va_lemma_Store(va_b106, va_s25, va_s24, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s107) == va_get_globals(va_old_s);  // line 489 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s107));
    assert global_non_scratchpad_vars_are_unchanged(va_get_globals(va_old_s),
      va_get_globals(va_s107));  // line 491 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.vad
    va_s24 := va_lemma_empty(va_s107, va_s24);
  }
  ghost var va_b111, va_s111 := va_lemma_POP_Reg1ToReg6(va_b24, va_s24, va_sM);
  ghost var va_b112, va_s112 := va_lemma_POP_OneReg(va_b111, va_s111, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s112, va_sM);
}
//--
