include "../../ins/x86/ins_wrapper.gen.dfy"
include "usb_def.dfy"
include "usb_tds_utils.i.dfy"
include "usb_tds_validstate.i.dfy"
include "..\\..\\drv\\public\\wimpdrv_lemmas.i.dfy"
//-- usbtd_get_td_vaddr

function method{:opaque} va_code_usbtd_get_td_vaddr(slot:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDI), va_coerce_reg_to_word(slot)),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_TD_BytesOffset)), va_CCons(va_code_ADD(va_op_word_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(EDX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))
}

lemma va_lemma_usbtd_get_td_vaddr(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  slot:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_get_td_vaddr(slot), va_s0, va_sN)
  requires va_is_src_reg(slot, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires slot == Reg1
  requires var stack_req_space := 3 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires usbtd_map_valid_slot_id(va_eval_reg(va_s0, slot))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var vaddr := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); vaddr ==
    AddressOfGlobal(G_USBTD_MAP_MEM()) + va_eval_reg(va_sM, slot) * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_TD_BytesOffset
  ensures  va_eval_reg(va_sM, slot) == va_eval_reg(va_s0, slot)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EAX, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbtd_get_td_vaddr();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b6, va_s6 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b7, va_s7 := va_lemma_LDRglobaladdr_ToReg(va_b6, va_s6, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b8, va_s8 := va_lemma_MOV_ToReg(va_b7, va_s7, va_sM, va_op_reg_reg(EDI),
    va_coerce_reg_to_word(slot));
  Lemma_NatMul_Ineq_4var(va_eval_reg(va_s8, slot), G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM,
    G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(va_eval_reg(va_s8, slot) * G_USBTDs_MAP_ENTRY_SZ);  // line 63 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b11, va_s11 := va_lemma_MUL_Reg_32BitsResult(va_b8, va_s8, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b12, va_s12 := va_lemma_ADD(va_b11, va_s11, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_TD_BytesOffset));
  Lemma_usbtd_get_td_vaddr_result_is_gvar_valid_addr(va_get_reg(EDX, va_s12), va_eval_reg(va_s12,
    slot), va_get_reg(EDI, va_s12));
  ghost var va_b14, va_s14 := va_lemma_ADD(va_b12, va_s12, va_sM, va_op_word_reg(EDX),
    va_op_word_reg(EDI));
  ghost var va_b15, va_s15 := va_lemma_Store(va_b14, va_s14, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(EDX));
  ghost var va_b16, va_s16 := va_lemma_POP_TwoRegs(va_b15, va_s15, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b17, va_s17 := va_lemma_POP_OneReg(va_b16, va_s16, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s17, va_sM);
}
//--
//-- usbtd_get_id

function method{:opaque} va_code_usbtd_get_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_ID_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_USBTD_MAP_MEM(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_get_id(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_get_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var ret_v :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var addr :=
    AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_ID_BytesOffset; is_gvar_valid_addr(G_USBTD_MAP_MEM(), addr) && ret_v ==
    global_read_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), addr)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EAX, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbtd_get_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 140 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_ID_BytesOffset));
  Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset);
  ghost var va_b17, va_s17 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s17, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(ESI));
  ghost var va_b20, va_s20 := va_lemma_POP_TwoRegs(va_b19, va_s19, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b20, va_s20, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s21, va_sM);
}
//--
//-- usbtd_get_type

function method{:opaque} va_code_usbtd_get_type():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_TYPE_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_USBTD_MAP_MEM(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_get_type(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_get_type(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var ret_type
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var addr :=
    AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_TYPE_BytesOffset; is_gvar_valid_addr(G_USBTD_MAP_MEM(), addr) && ret_type ==
    global_read_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), addr)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EAX, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbtd_get_type();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 217 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_TYPE_BytesOffset));
  Lemma_usbtd_get_td_type_result_is_gvar_valid_addr(va_get_reg(EDX, va_s15), slot, va_get_reg(EDI,
    va_s15));
  ghost var va_b17, va_s17 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s17, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(ESI));
  ghost var va_b20, va_s20 := va_lemma_POP_TwoRegs(va_b19, va_s19, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b20, va_s20, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s21, va_sM);
}
//--
//-- usbtd_get_bus_id

function method{:opaque} va_code_usbtd_get_bus_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_BUSID_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_USBTD_MAP_MEM(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_get_bus_id(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_get_bus_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var ret_v :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var addr :=
    AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_BUSID_BytesOffset; is_gvar_valid_addr(G_USBTD_MAP_MEM(), addr) && ret_v ==
    global_read_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), addr)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EAX, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbtd_get_bus_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 294 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_BUSID_BytesOffset));
  Lemma_usbtd_get_bus_id_result_is_gvar_valid_addr(va_get_reg(EDX, va_s15), slot, va_get_reg(EDI,
    va_s15));
  ghost var va_b17, va_s17 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s17, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(ESI));
  ghost var va_b20, va_s20 := va_lemma_POP_TwoRegs(va_b19, va_s19, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b20, va_s20, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s21, va_sM);
}
//--
//-- usbtd_get_wimpdrv_slotid

function method{:opaque} va_code_usbtd_get_wimpdrv_slotid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_USBTD_MAP_MEM(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_get_wimpdrv_slotid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_get_wimpdrv_slotid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var ret_v :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var addr :=
    AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset; is_gvar_valid_addr(G_USBTD_MAP_MEM(), addr) &&
    ret_v == global_read_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), addr)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EAX, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbtd_get_wimpdrv_slotid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 372 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset));
  Lemma_usbtd_get_wimpdrv_slotid_result_is_gvar_valid_addr(va_get_reg(EDX, va_s15), slot,
    va_get_reg(EDI, va_s15));
  ghost var va_b17, va_s17 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s17, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(ESI));
  ghost var va_b20, va_s20 := va_lemma_POP_TwoRegs(va_b19, va_s19, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b20, va_s20, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s21, va_sM);
}
//--
//-- usbtd_check_wimpdrv_slotid

function method{:opaque} va_code_usbtd_check_wimpdrv_slotid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EDX)), va_CCons(va_code_Load(va_op_word_reg(EDX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDX)),
    va_CCons(va_code_usbtd_get_wimpdrv_slotid(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))
}

lemma va_lemma_usbtd_check_wimpdrv_slotid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_check_wimpdrv_slotid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var td_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var expect_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var td_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    var ret := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ret == TRUE <==>
    usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s0), td_slot) == expect_v
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EAX, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbtd_check_wimpdrv_slotid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(EDX));
  ghost var va_b9, va_s9 := va_lemma_Load(va_b8, va_s8, va_sM, va_op_word_reg(EDX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b10, va_s10 := va_lemma_PUSH(va_b9, va_s9, va_sM, va_op_word_reg(EDX));
  ghost var va_b11, va_s11 := va_lemma_usbtd_get_wimpdrv_slotid(va_b10, va_s10, va_sM);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0);
  ghost var va_b13, va_s13 := va_lemma_POP_VOID(va_b12, va_s12, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b14, va_s14 := va_lemma_Load(va_b13, va_s13, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_s15, va_c15, va_b15 := va_lemma_block(va_b14, va_s14, va_sM);
  ghost var va_cond_c15, va_s16:va_state := va_lemma_ifElse(va_get_ifCond(va_c15),
    va_get_ifTrue(va_c15), va_get_ifFalse(va_c15), va_s14, va_s15);
  if (va_cond_c15)
  {
    ghost var va_b17 := va_get_block(va_get_ifTrue(va_c15));
    ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s16, va_s15, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    va_s15 := va_lemma_empty(va_s18, va_s15);
  }
  else
  {
    ghost var va_b19 := va_get_block(va_get_ifFalse(va_c15));
    ghost var va_b20, va_s20 := va_lemma_Store(va_b19, va_s16, va_s15, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s15 := va_lemma_empty(va_s20, va_s15);
  }
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b15, va_s15, va_sM, va_op_reg_reg(EDX));
  ghost var va_b22, va_s22 := va_lemma_POP_TwoRegs(va_b21, va_s21, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b23, va_s23 := va_lemma_POP_OneReg(va_b22, va_s22, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s23, va_sM);
}
//--
//-- usbtd_get_usbpdev_slotid

function method{:opaque} va_code_usbtd_get_usbpdev_slotid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_USBTD_MAP_MEM(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_get_usbpdev_slotid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_get_usbpdev_slotid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var ret_v :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var addr :=
    AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset; is_gvar_valid_addr(G_USBTD_MAP_MEM(), addr) &&
    ret_v == global_read_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), addr)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EAX, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbtd_get_usbpdev_slotid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 528 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset));
  Lemma_usbtd_get_usbpdev_slotid_result_is_gvar_valid_addr(va_get_reg(EDX, va_s15), slot,
    va_get_reg(EDI, va_s15));
  ghost var va_b17, va_s17 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s17, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(ESI));
  ghost var va_b20, va_s20 := va_lemma_POP_TwoRegs(va_b19, va_s19, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b20, va_s20, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s21, va_sM);
}
//--
//-- usbtd_check_usbpdev_slotid

function method{:opaque} va_code_usbtd_check_usbpdev_slotid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EDX)), va_CCons(va_code_Load(va_op_word_reg(EDX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDX)),
    va_CCons(va_code_usbtd_get_usbpdev_slotid(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))
}

lemma va_lemma_usbtd_check_usbpdev_slotid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_check_usbpdev_slotid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var td_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var expect_v:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var td_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    var ret := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ret == TRUE <==>
    usbtd_map_get_usbpdev_slotid(va_get_globals(va_s0), td_slot) == expect_v
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EAX, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbtd_check_usbpdev_slotid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(EDX));
  ghost var va_b9, va_s9 := va_lemma_Load(va_b8, va_s8, va_sM, va_op_word_reg(EDX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b10, va_s10 := va_lemma_PUSH(va_b9, va_s9, va_sM, va_op_word_reg(EDX));
  ghost var va_b11, va_s11 := va_lemma_usbtd_get_usbpdev_slotid(va_b10, va_s10, va_sM);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0);
  ghost var va_b13, va_s13 := va_lemma_POP_VOID(va_b12, va_s12, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b14, va_s14 := va_lemma_Load(va_b13, va_s13, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_s15, va_c15, va_b15 := va_lemma_block(va_b14, va_s14, va_sM);
  ghost var va_cond_c15, va_s16:va_state := va_lemma_ifElse(va_get_ifCond(va_c15),
    va_get_ifTrue(va_c15), va_get_ifFalse(va_c15), va_s14, va_s15);
  if (va_cond_c15)
  {
    ghost var va_b17 := va_get_block(va_get_ifTrue(va_c15));
    ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s16, va_s15, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    va_s15 := va_lemma_empty(va_s18, va_s15);
  }
  else
  {
    ghost var va_b19 := va_get_block(va_get_ifFalse(va_c15));
    ghost var va_b20, va_s20 := va_lemma_Store(va_b19, va_s16, va_s15, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s15 := va_lemma_empty(va_s20, va_s15);
  }
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b15, va_s15, va_sM, va_op_reg_reg(EDX));
  ghost var va_b22, va_s22 := va_lemma_POP_TwoRegs(va_b21, va_s21, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b23, va_s23 := va_lemma_POP_OneReg(va_b22, va_s22, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s23, va_sM);
}
//--
//-- usbtd_get_td_pid

function method{:opaque} va_code_usbtd_get_td_pid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_PID_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_USBTD_MAP_MEM(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_get_td_pid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_get_td_pid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    out_pid:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    usbtd_map_get_pid(va_get_globals(va_s0), in_slot) == WS_PartitionID(out_pid)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_reg(EAX, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbtd_get_td_pid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 680 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_PID_BytesOffset));
  Lemma_usbtd_get_td_pid_result_is_gvar_valid_addr(va_get_reg(EDX, va_s15), slot, va_get_reg(EDI,
    va_s15));
  ghost var va_b17, va_s17 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s17, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(ESI));
  ghost var va_b20, va_s20 := va_lemma_POP_TwoRegs(va_b19, va_s19, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b20, va_s20, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s21, va_sM);
}
//--
//-- usbtd_check_td_slot_id

function method{:opaque} va_code_usbtd_check_td_slot_id(slot_id:va_operand_reg,
  ret:va_operand_reg):va_code
{
  va_Block(va_CCons(va_IfElse(va_cmp_ge(va_coerce_reg_to_cmp(slot_id), va_const_cmp(0)),
    va_Block(va_CCons(va_IfElse(va_cmp_lt(va_coerce_reg_to_cmp(slot_id),
    va_const_cmp(USB_TD_ENTRY_NUM)), va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(FALSE)), va_CNil()))),
    va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(FALSE)), va_CNil()))),
    va_CNil()))
}

lemma va_lemma_usbtd_check_td_slot_id(va_b0:va_codes, va_s0:va_state, va_sN:va_state,
  slot_id:va_operand_reg, ret:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_check_td_slot_id(slot_id, ret), va_s0, va_sN)
  requires va_is_src_reg(slot_id, va_s0)
  requires va_is_dst_reg(ret, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires slot_id != ret
  requires ret == Reg1
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  va_eval_reg(va_sM, ret) == TRUE ==> usbtd_map_valid_slot_id(va_eval_reg(va_sM, slot_id))
  ensures  va_get_mem(va_s0) == va_get_mem(va_sM)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_ok(va_sM, va_update_operand_reg(ret, va_sM, va_s0)))
{
  reveal_va_code_usbtd_check_td_slot_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_s2, va_c2, va_b2 := va_lemma_block(va_b1, va_s0, va_sM);
  ghost var va_cond_c2, va_s3:va_state := va_lemma_ifElse(va_get_ifCond(va_c2),
    va_get_ifTrue(va_c2), va_get_ifFalse(va_c2), va_s0, va_s2);
  if (va_cond_c2)
  {
    ghost var va_b4 := va_get_block(va_get_ifTrue(va_c2));
    ghost var va_s5, va_c5, va_b5 := va_lemma_block(va_b4, va_s3, va_s2);
    ghost var va_cond_c5, va_s6:va_state := va_lemma_ifElse(va_get_ifCond(va_c5),
      va_get_ifTrue(va_c5), va_get_ifFalse(va_c5), va_s3, va_s5);
    if (va_cond_c5)
    {
      ghost var va_b7 := va_get_block(va_get_ifTrue(va_c5));
      ghost var va_b8, va_s8 := va_lemma_MOV_ToReg(va_b7, va_s6, va_s5, ret, va_const_word(TRUE));
      va_s5 := va_lemma_empty(va_s8, va_s5);
    }
    else
    {
      ghost var va_b9 := va_get_block(va_get_ifFalse(va_c5));
      ghost var va_b10, va_s10 := va_lemma_MOV_ToReg(va_b9, va_s6, va_s5, ret,
        va_const_word(FALSE));
      va_s5 := va_lemma_empty(va_s10, va_s5);
    }
    va_s2 := va_lemma_empty(va_s5, va_s2);
  }
  else
  {
    ghost var va_b11 := va_get_block(va_get_ifFalse(va_c2));
    ghost var va_b12, va_s12 := va_lemma_MOV_ToReg(va_b11, va_s3, va_s2, ret, va_const_word(FALSE));
    va_s2 := va_lemma_empty(va_s12, va_s2);
  }
  va_sM := va_lemma_empty(va_s2, va_sM);
}
//--
//-- usbtd_check_and_get_td_pid

function method{:opaque} va_code_usbtd_check_and_get_td_pid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_ge(va_op_cmp_reg(EDI), va_const_cmp(0)),
    va_Block(va_CCons(va_IfElse(va_cmp_lt(va_op_cmp_reg(EDI), va_const_cmp(USB_TD_ENTRY_NUM)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_usbtd_get_td_pid(),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))
}

lemma va_lemma_usbtd_check_and_get_td_pid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_check_and_get_td_pid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 3 * ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var out_pid:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); (ret == TRUE ==>
    usbtd_map_valid_slot_id(in_slot)) && (ret == TRUE ==> usbtd_map_get_pid(va_get_globals(va_s0),
    in_slot) == WS_PartitionID(out_pid))
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_reg(EAX, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbtd_check_and_get_td_pid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b6, va_s6 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b7, va_s7 := va_lemma_Load(va_b6, va_s6, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_s8, va_c8, va_b8 := va_lemma_block(va_b7, va_s7, va_sM);
  ghost var va_cond_c8, va_s9:va_state := va_lemma_ifElse(va_get_ifCond(va_c8),
    va_get_ifTrue(va_c8), va_get_ifFalse(va_c8), va_s7, va_s8);
  if (va_cond_c8)
  {
    ghost var va_b10 := va_get_block(va_get_ifTrue(va_c8));
    ghost var va_s11, va_c11, va_b11 := va_lemma_block(va_b10, va_s9, va_s8);
    ghost var va_cond_c11, va_s12:va_state := va_lemma_ifElse(va_get_ifCond(va_c11),
      va_get_ifTrue(va_c11), va_get_ifFalse(va_c11), va_s9, va_s11);
    if (va_cond_c11)
    {
      ghost var va_b13 := va_get_block(va_get_ifTrue(va_c11));
      ghost var va_b14, va_s14 := va_lemma_PUSH(va_b13, va_s12, va_s11, va_op_word_reg(EDI));
      ghost var va_b15, va_s15 := va_lemma_usbtd_get_td_pid(va_b14, va_s14, va_s11);
      ghost var va_b16, va_s16 := va_lemma_Load(va_b15, va_s15, va_s11, va_op_word_reg(ESI),
        va_op_word_reg(ESP), 0);
      ghost var va_b17, va_s17 := va_lemma_POP_VOID(va_b16, va_s16, va_s11, 1 * ARCH_WORD_BYTES);
      ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s17, va_s11, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      ghost var va_b19, va_s19 := va_lemma_Store(va_b18, va_s18, va_s11, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_op_word_reg(ESI));
      va_s11 := va_lemma_empty(va_s19, va_s11);
    }
    else
    {
      ghost var va_b20 := va_get_block(va_get_ifFalse(va_c11));
      ghost var va_b21, va_s21 := va_lemma_Store(va_b20, va_s12, va_s11, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      va_s11 := va_lemma_empty(va_s21, va_s11);
    }
    va_s8 := va_lemma_empty(va_s11, va_s8);
  }
  else
  {
    ghost var va_b22 := va_get_block(va_get_ifFalse(va_c8));
    ghost var va_b23, va_s23 := va_lemma_Store(va_b22, va_s9, va_s8, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s8 := va_lemma_empty(va_s23, va_s8);
  }
  ghost var va_b24, va_s24 := va_lemma_POP_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b25, va_s25 := va_lemma_POP_OneReg(va_b24, va_s24, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s25, va_sM);
}
//--
//-- usbtd_get_flags

function method{:opaque} va_code_usbtd_get_flags():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_USBTD_MAP_MEM(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_get_flags(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_get_flags(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    out_flags:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    usbtd_map_get_flags(va_get_globals(va_s0), in_slot) == out_flags
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code_usbtd_get_flags();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 868 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset));
  Lemma_usbtd_get_flag_result_is_gvar_valid_addr(va_get_reg(EDX, va_s15), slot, va_get_reg(EDI,
    va_s15));
  ghost var va_b17, va_s17 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s17, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b19, va_s19 := va_lemma_POP_OneReg(va_b18, va_s18, va_sM, va_op_reg_reg(ESI));
  ghost var va_b20, va_s20 := va_lemma_POP_TwoRegs(va_b19, va_s19, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b20, va_s20, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s21, va_sM);
}
//--
//-- usbtd_check_flags_slotsecure

function method{:opaque} va_code_usbtd_check_flags_slotsecure():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EDX)), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(ESI)),
    va_CCons(va_code_usbtd_get_flags(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_TestBit(va_op_word_reg(EDI), USBTD_SLOT_FLAG_SlotSecure_Bit,
    va_op_word_reg(EDX)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(EDX)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))
}

lemma va_lemma_usbtd_check_flags_slotsecure(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_check_flags_slotsecure(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(in_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ret == TRUE ==>
    TestBit(usbtd_map_get_flags(va_get_globals(va_s0), in_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP, va_sM, va_update_ok(va_sM,
    va_s0))))))))))
{
  reveal_va_code_usbtd_check_flags_slotsecure();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(EDX));
  ghost var va_b9, va_s9 := va_lemma_Load(va_b8, va_s8, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b10, va_s10 := va_lemma_PUSH(va_b9, va_s9, va_sM, va_op_word_reg(ESI));
  ghost var va_b11, va_s11 := va_lemma_usbtd_get_flags(va_b10, va_s10, va_sM);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0);
  ghost var va_b13, va_s13 := va_lemma_POP_VOID(va_b12, va_s12, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b14, va_s14 := va_lemma_TestBit(va_b13, va_s13, va_sM, va_op_word_reg(EDI),
    USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX));
  ghost var va_b15, va_s15 := va_lemma_Store(va_b14, va_s14, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(EDX));
  ghost var va_b16, va_s16 := va_lemma_POP_OneReg(va_b15, va_s15, va_sM, va_op_reg_reg(EDX));
  ghost var va_b17, va_s17 := va_lemma_POP_TwoRegs(va_b16, va_s16, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDI));
  ghost var va_b18, va_s18 := va_lemma_POP_OneReg(va_b17, va_s17, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s18, va_sM);
}
//--
//-- usbtd_set_td_pid

function method{:opaque} va_code_usbtd_set_td_pid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_PID_BytesOffset)),
    va_CCons(va_code_STRglobal(G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_set_td_pid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_set_td_pid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot) && eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_s0), slot)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    (new_pid == PID_INVALID || WS_PartitionID(new_pid) in
    pids_parse_g_wimp_pids(va_get_globals(va_s0))) && (new_pid != PID_INVALID ==>
    usbtd_map_get_idword(va_get_globals(va_s0), slot) != USBTD_ID_INVALID)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    TestBit(usbtd_map_get_flags(va_get_globals(va_s0), slot), USBTD_SLOT_FLAG_SlotSecure_Bit) ==
    false
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    usbtd_map_get_pid(va_get_globals(va_sM), in_slot) == WS_PartitionID(new_pid)
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var
    vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + in_slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_PID_BytesOffset; is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
    va_get_globals(va_sM) == global_write_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), vaddr,
    new_pid)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_reg(EAX, va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))
{
  reveal_va_code_usbtd_set_td_pid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s11);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 1039 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b15, va_s15 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b16, va_s16 := va_lemma_ADD(va_b15, va_s15, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_PID_BytesOffset));
  Lemma_usbtd_get_td_pid_result_is_gvar_valid_addr(va_get_reg(EDX, va_s16), slot, va_get_reg(EDI,
    va_s16));
  ghost var tmp_addr1 := va_get_reg(EDX, va_s16) + va_get_reg(EDI, va_s16);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s16), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s16));
  ghost var new_this1 := va_s16.(wk_mstate := va_s16.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfNewPIDOfSlotIsGood(va_s16, new_this1, slot,
    va_get_reg(EDX, va_s16) + va_get_reg(EDI, va_s16), va_get_reg(ESI, va_s16));
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdatePIDOfEEHCIUnrefedUSBTD(va_get_globals(va_s16),
    new_globals1, slot, tmp_addr1, va_get_reg(ESI, va_s16));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s16,
    new_this1);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s16,
    new_this1);
  assert ins_valid_strglobal_word(va_s16.subjects, va_s16.objects, va_s16.id_mappings,
    va_s16.objs_addrs, va_s16.activate_conds, va_get_globals(va_s16), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s16));  // line 1061 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b31, va_s31 := va_lemma_STRglobal(va_b16, va_s16, va_sM, G_USBTD_MAP_MEM(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingInsecureUSBTDAndNotFlags(va_get_globals(va_old_s),
    va_get_globals(va_s31), slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset, va_get_reg(ESI, va_s31));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s31);
  ghost var va_b34, va_s34 := va_lemma_POP_OneReg(va_b31, va_s31, va_sM, va_op_reg_reg(ESI));
  ghost var va_b35, va_s35 := va_lemma_POP_TwoRegs(va_b34, va_s34, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b36, va_s36 := va_lemma_POP_OneReg(va_b35, va_s35, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s36, va_sM);
}
//--
//-- usbtd_set_td_type

function method{:opaque} va_code_usbtd_set_td_type():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_TYPE_BytesOffset)),
    va_CCons(va_code_STRglobal(G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_set_td_type(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_set_td_type(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires var new_type:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); ((new_type == USBTDs_TYPE_QTD32 || new_type == USBTDs_TYPE_QH32) || new_type
    == USBTDs_TYPE_iTD32) || new_type == USBTDs_TYPE_siTD32
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    TestBit(usbtd_map_get_flags(va_get_globals(va_s0), slot), USBTD_SLOT_FLAG_SlotSecure_Bit) ==
    false
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_type:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    usbtd_map_get_type(va_get_globals(va_sM), in_slot) == new_type
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_type:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + in_slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_TYPE_BytesOffset; is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
    va_get_globals(va_sM) == global_write_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), vaddr,
    new_type)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_reg(EAX, va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))
{
  reveal_va_code_usbtd_set_td_type();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s11);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 1159 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b15, va_s15 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b16, va_s16 := va_lemma_ADD(va_b15, va_s15, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_TYPE_BytesOffset));
  Lemma_usbtd_get_td_type_result_is_gvar_valid_addr(va_get_reg(EDX, va_s16), slot, va_get_reg(EDI,
    va_s16));
  ghost var tmp_addr1 := va_get_reg(EDX, va_s16) + va_get_reg(EDI, va_s16);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s16), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s16));
  ghost var new_this1 := va_s16.(wk_mstate := va_s16.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfNewTypeOfSlotIsValid(va_get_globals(va_s16),
    new_globals1, slot, va_get_reg(EDX, va_s16) + va_get_reg(EDI, va_s16), va_get_reg(ESI, va_s16));
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateTypeOfUSBTD(va_get_globals(va_s16),
    new_globals1, slot, tmp_addr1, va_get_reg(ESI, va_s16));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s16,
    new_this1);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s16,
    new_this1);
  assert ins_valid_strglobal_word(va_s16.subjects, va_s16.objects, va_s16.id_mappings,
    va_s16.objs_addrs, va_s16.activate_conds, va_get_globals(va_s16), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s16));  // line 1184 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b33, va_s33 := va_lemma_STRglobal(va_b16, va_s16, va_sM, G_USBTD_MAP_MEM(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingInsecureUSBTDAndNotFlags(va_get_globals(va_old_s),
    va_get_globals(va_s33), slot, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, va_get_reg(ESI, va_s33));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s33);
  ghost var va_b36, va_s36 := va_lemma_POP_OneReg(va_b33, va_s33, va_sM, va_op_reg_reg(ESI));
  ghost var va_b37, va_s37 := va_lemma_POP_TwoRegs(va_b36, va_s36, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b38, va_s38 := va_lemma_POP_OneReg(va_b37, va_s37, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s38, va_sM);
}
//--
//-- usbtd_set_bus_id

function method{:opaque} va_code_usbtd_set_bus_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_BUSID_BytesOffset)),
    va_CCons(va_code_STRglobal(G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_set_bus_id(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_set_bus_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot) && eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_s0), slot)
  requires var new_bus_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); isUInt16(new_bus_id)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    TestBit(usbtd_map_get_flags(va_get_globals(va_s0), slot), USBTD_SLOT_FLAG_SlotSecure_Bit) ==
    false
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_bus_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    usbtd_map_get_busid(va_get_globals(va_sM), in_slot) == new_bus_id
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_bus_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + in_slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_BUSID_BytesOffset; is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
    va_get_globals(va_sM) == global_write_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), vaddr,
    new_bus_id)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_reg(EAX, va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))
{
  reveal_va_code_usbtd_set_bus_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var cur_esp := va_get_reg(ESP, va_s8);
  ghost var va_b10, va_s10 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s12);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 1284 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b16, va_s16 := va_lemma_MUL_Reg_32BitsResult(va_b12, va_s12, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b17, va_s17 := va_lemma_ADD(va_b16, va_s16, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_BUSID_BytesOffset));
  Lemma_usbtd_get_bus_id_result_is_gvar_valid_addr(va_get_reg(EDX, va_s17), slot, va_get_reg(EDI,
    va_s17));
  ghost var tmp_addr1 := va_get_reg(EDX, va_s17) + va_get_reg(EDI, va_s17);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s17), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s17));
  ghost var new_this1 := va_s17.(wk_mstate := va_s17.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s17),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s17),
    new_globals1);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s17),
    new_globals1);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s17),
    new_globals1);
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfNewBusIDIsValid(va_get_globals(va_s17),
    new_globals1, slot, tmp_addr1, va_get_reg(ESI, va_s17));
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s17),
    new_globals1);
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(va_get_globals(va_s17), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, va_get_reg(ESI, va_s17));
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(va_get_globals(va_s17), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, va_get_reg(ESI, va_s17));
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateBusIDOfEEHCIUnrefedUSBTD(va_get_globals(va_s17),
    new_globals1, slot, tmp_addr1, va_get_reg(ESI, va_s17));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s17,
    new_this1);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s17,
    new_this1);
  assert ins_valid_strglobal_word(va_s17.subjects, va_s17.objects, va_s17.id_mappings,
    va_s17.objs_addrs, va_s17.activate_conds, va_get_globals(va_s17), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s17));  // line 1309 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b34, va_s34 := va_lemma_STRglobal(va_b17, va_s17, va_sM, G_USBTD_MAP_MEM(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingInsecureUSBTDAndNotFlags(va_get_globals(va_old_s),
    va_get_globals(va_s34), slot, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, va_get_reg(ESI, va_s34));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s34);
  assert va_get_reg(ESP, va_s34) == cur_esp;  // line 1320 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b38, va_s38 := va_lemma_POP_OneReg(va_b34, va_s34, va_sM, va_op_reg_reg(ESI));
  ghost var va_b39, va_s39 := va_lemma_POP_TwoRegs(va_b38, va_s38, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b40, va_s40 := va_lemma_POP_OneReg(va_b39, va_s39, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s40, va_sM);
}
//--
//-- usbtd_set_wimpdrv_slotid

function method{:opaque} va_code_usbtd_set_wimpdrv_slotid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset)),
    va_CCons(va_code_STRglobal(G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_set_wimpdrv_slotid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_set_wimpdrv_slotid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires var new_wimpdrv_slotid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); new_wimpdrv_slotid == WimpDrv_SlotID_EMPTY ||
    wimpdrv_valid_slot_id(new_wimpdrv_slotid)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    TestBit(usbtd_map_get_flags(va_get_globals(va_s0), slot), USBTD_SLOT_FLAG_SlotSecure_Bit) ==
    false
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_wimpdrv_slotid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); usbtd_map_get_wimpdrv_slotid(va_get_globals(va_sM), in_slot) ==
    new_wimpdrv_slotid
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_wimpdrv_slotid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + in_slot *
    G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;
    is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) && va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), vaddr, new_wimpdrv_slotid)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_reg(EAX, va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))
{
  reveal_va_code_usbtd_set_wimpdrv_slotid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s11);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 1408 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b15, va_s15 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b16, va_s16 := va_lemma_ADD(va_b15, va_s15, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset));
  Lemma_usbtd_get_wimpdrv_slotid_result_is_gvar_valid_addr(va_get_reg(EDX, va_s16), slot,
    va_get_reg(EDI, va_s16));
  assert is_gvar_valid_addr(G_USBTD_MAP_MEM(), va_get_reg(EDX, va_s16) + va_get_reg(EDI, va_s16)); 
    // line 1413 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var tmp_addr1 := va_get_reg(EDX, va_s16) + va_get_reg(EDI, va_s16);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s16), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s16));
  ghost var new_this1 := va_s16.(wk_mstate := va_s16.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(va_get_globals(va_s16),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(va_get_globals(va_s16),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfNewWimpDrvSlotIDOfSlotIsValid(va_get_globals(va_s16),
    new_globals1, slot, tmp_addr1, va_get_reg(ESI, va_s16));
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateWimpDrvSlotIDOfUSBTD(va_get_globals(va_s16),
    new_globals1, slot, tmp_addr1, va_get_reg(ESI, va_s16));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s16,
    new_this1);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s16,
    new_this1);
  assert ins_valid_strglobal_word(va_s16.subjects, va_s16.objects, va_s16.id_mappings,
    va_s16.objs_addrs, va_s16.activate_conds, va_get_globals(va_s16), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s16));  // line 1439 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b39, va_s39 := va_lemma_STRglobal(va_b16, va_s16, va_sM, G_USBTD_MAP_MEM(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingInsecureUSBTDAndNotFlags(va_get_globals(va_old_s),
    va_get_globals(va_s39), slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, va_get_reg(ESI,
    va_s39));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s39);
  ghost var va_b42, va_s42 := va_lemma_POP_OneReg(va_b39, va_s39, va_sM, va_op_reg_reg(ESI));
  ghost var va_b43, va_s43 := va_lemma_POP_TwoRegs(va_b42, va_s42, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b44, va_s44 := va_lemma_POP_OneReg(va_b43, va_s43, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s44, va_sM);
}
//--
//-- usbtd_set_usbpdev_slotid

function method{:opaque} va_code_usbtd_set_usbpdev_slotid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset)),
    va_CCons(va_code_STRglobal(G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_set_usbpdev_slotid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_set_usbpdev_slotid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires var new_usbpdev_slotid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); new_usbpdev_slotid == WimpUSBPDev_SlotID_EMPTY ||
    usbpdev_valid_slot_id(new_usbpdev_slotid)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    TestBit(usbtd_map_get_flags(va_get_globals(va_s0), slot), USBTD_SLOT_FLAG_SlotSecure_Bit) ==
    false
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_usbpdev_slotid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); usbtd_map_get_usbpdev_slotid(va_get_globals(va_sM), in_slot) ==
    new_usbpdev_slotid
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_usbpdev_slotid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + in_slot *
    G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;
    is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) && va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), vaddr, new_usbpdev_slotid)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_reg(EAX, va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))
{
  reveal_va_code_usbtd_set_usbpdev_slotid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s11);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 1537 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b15, va_s15 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b16, va_s16 := va_lemma_ADD(va_b15, va_s15, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset));
  Lemma_usbtd_get_usbpdev_slotid_result_is_gvar_valid_addr(va_get_reg(EDX, va_s16), slot,
    va_get_reg(EDI, va_s16));
  assert is_gvar_valid_addr(G_USBTD_MAP_MEM(), va_get_reg(EDX, va_s16) + va_get_reg(EDI, va_s16)); 
    // line 1542 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var tmp_addr1 := va_get_reg(EDX, va_s16) + va_get_reg(EDI, va_s16);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s16), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s16));
  ghost var new_this1 := va_s16.(wk_mstate := va_s16.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(va_get_globals(va_s16),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(va_get_globals(va_s16),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfNewUSBPDevSlotIDOfSlotIsAllowed(va_get_globals(va_s16),
    new_globals1, slot, tmp_addr1, va_get_reg(ESI, va_s16));
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateUSBPDevSlotIDOfUSBTD(va_get_globals(va_s16),
    new_globals1, slot, tmp_addr1, va_get_reg(ESI, va_s16));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s16,
    new_this1);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s16,
    new_this1);
  assert ins_valid_strglobal_word(va_s16.subjects, va_s16.objects, va_s16.id_mappings,
    va_s16.objs_addrs, va_s16.activate_conds, va_get_globals(va_s16), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s16));  // line 1568 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b39, va_s39 := va_lemma_STRglobal(va_b16, va_s16, va_sM, G_USBTD_MAP_MEM(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingInsecureUSBTDAndNotFlags(va_get_globals(va_old_s),
    va_get_globals(va_s39), slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, va_get_reg(ESI,
    va_s39));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s39);
  ghost var va_b42, va_s42 := va_lemma_POP_OneReg(va_b39, va_s39, va_sM, va_op_reg_reg(ESI));
  ghost var va_b43, va_s43 := va_lemma_POP_TwoRegs(va_b42, va_s42, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b44, va_s44 := va_lemma_POP_OneReg(va_b43, va_s43, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s44, va_sM);
}
//--
//-- usbtd_set_flags

function method{:opaque} va_code_usbtd_set_flags():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset)),
    va_CCons(va_code_STRglobal(G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_set_flags(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_set_flags(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot) && eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_s0), slot)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_flags:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    var slot_type := usbtd_map_get_type(va_get_globals(va_s0), slot); ((((slot_type ==
    USBTDs_TYPE_QTD32 && TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit) ==>
    WK_USBTD_Map_SecureGlobalVarValues_qTD32(va_get_globals(va_s0), slot)) && (slot_type ==
    USBTDs_TYPE_QH32 && TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit) ==>
    WK_USBTD_Map_SecureGlobalVarValues_qh32(va_get_globals(va_s0), slot))) && (slot_type ==
    USBTDs_TYPE_iTD32 && TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit) ==>
    WK_USBTD_Map_SecureGlobalVarValues_iTD32(va_get_globals(va_s0), slot))) && (slot_type ==
    USBTDs_TYPE_siTD32 && TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit) ==>
    WK_USBTD_Map_SecureGlobalVarValues_siTD32(va_get_globals(va_s0), slot))) && (TestBit(new_flags,
    USBTD_SLOT_FLAG_SlotSecure_Bit) == false ==>
    usbtds_verifiedtds_do_not_associate_usbtd(va_get_globals(va_s0), slot))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_flags:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    usbtd_map_get_flags(va_get_globals(va_sM), in_slot) == new_flags
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_flags:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + in_slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset; is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
    va_get_globals(va_sM) == global_write_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), vaddr,
    new_flags)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_reg(EAX, va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))
{
  reveal_va_code_usbtd_set_flags();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s11);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 1678 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b15, va_s15 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b16, va_s16 := va_lemma_ADD(va_b15, va_s15, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset));
  Lemma_usbtd_get_flag_result_is_gvar_valid_addr(va_get_reg(EDX, va_s16), slot, va_get_reg(EDI,
    va_s16));
  ghost var tmp_addr1 := va_get_reg(EDX, va_s16) + va_get_reg(EDI, va_s16);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s16), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s16));
  ghost var new_this1 := va_s16.(wk_mstate := va_s16.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(va_get_globals(va_s16),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(va_get_globals(va_s16),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(va_get_globals(va_s16),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfPIDTypeBusIDWimpDrvSlotIDUSBPDevSlotID_FieldsAreUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateFlagOfEEHCIUnrefedUSBTD(va_get_globals(va_s16),
    new_globals1, slot, tmp_addr1, va_get_reg(ESI, va_s16));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s16,
    new_this1);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s16,
    new_this1);
  assert ins_valid_strglobal_word(va_s16.subjects, va_s16.objects, va_s16.id_mappings,
    va_s16.objs_addrs, va_s16.activate_conds, va_get_globals(va_s16), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s16));  // line 1708 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b38, va_s38 := va_lemma_STRglobal(va_b16, va_s16, va_sM, G_USBTD_MAP_MEM(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingFlagsOfUSBTDs(va_get_globals(va_old_s),
    va_get_globals(va_s38), slot, va_get_reg(ESI, va_s38));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s38);
  ghost var va_b41, va_s41 := va_lemma_POP_OneReg(va_b38, va_s38, va_sM, va_op_reg_reg(ESI));
  ghost var va_b42, va_s42 := va_lemma_POP_TwoRegs(va_b41, va_s41, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b43, va_s43 := va_lemma_POP_OneReg(va_b42, va_s42, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s43, va_sM);
}
//--
//-- usbtd_set_handle

function method{:opaque} va_code_usbtd_set_handle():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset)),
    va_CCons(va_code_STRglobal(G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_set_handle(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_set_handle(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_handle:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    usbtd_map_get_handle(va_get_globals(va_sM), in_slot) == new_handle
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_handle:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + in_slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset; is_gvar_valid_addr(G_USBTD_MAP_MEM(),
    vaddr) && va_get_globals(va_sM) == global_write_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(),
    vaddr, new_handle)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_reg(EAX, va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))
{
  reveal_va_code_usbtd_set_handle();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var va_b9, va_s9 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s11);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 1796 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b15, va_s15 := va_lemma_MUL_Reg_32BitsResult(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b16, va_s16 := va_lemma_ADD(va_b15, va_s15, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset));
  Lemma_usbtd_get_handle_result_is_gvar_valid_addr(va_get_reg(EDX, va_s16), slot, va_get_reg(EDI,
    va_s16));
  ghost var tmp_addr1 := va_get_reg(EDX, va_s16) + va_get_reg(EDI, va_s16);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s16), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s16));
  ghost var new_this1 := va_s16.(wk_mstate := va_s16.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(va_get_globals(va_s16),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, va_get_reg(ESI,
    va_s16));
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(va_get_globals(va_s16), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, va_get_reg(ESI, va_s16));
  Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(va_get_globals(va_s16),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, va_get_reg(ESI,
    va_s16));
  Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(va_get_globals(va_s16),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, va_get_reg(ESI,
    va_s16));
  Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfPIDTypeBusIDWimpDrvSlotIDUSBPDevSlotID_FieldsAreUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s16),
    new_globals1);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateHandleOfUSBTD(va_get_globals(va_s16),
    new_globals1, slot, tmp_addr1, va_get_reg(ESI, va_s16));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s16,
    new_this1);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s16,
    new_this1);
  assert ins_valid_strglobal_word(va_s16.subjects, va_s16.objects, va_s16.id_mappings,
    va_s16.objs_addrs, va_s16.activate_conds, va_get_globals(va_s16), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s16));  // line 1827 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b39, va_s39 := va_lemma_STRglobal(va_b16, va_s16, va_sM, G_USBTD_MAP_MEM(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfMostUSBTDsFieldAndWimpDrvsAndUSBPDevsAreUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_s39));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s39);
  ghost var va_b42, va_s42 := va_lemma_POP_OneReg(va_b39, va_s39, va_sM, va_op_reg_reg(ESI));
  ghost var va_b43, va_s43 := va_lemma_POP_TwoRegs(va_b42, va_s42, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b44, va_s44 := va_lemma_POP_OneReg(va_b43, va_s43, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s44, va_sM);
}
//--
//-- usbtd_set_inputparams

function method{:opaque} va_code_usbtd_set_inputparams():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX),
    va_const_cmp(G_USBTDs_MAP_ENTRY_InputParam1)),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset)), va_CNil())),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX),
    va_const_cmp(G_USBTDs_MAP_ENTRY_InputParam2)),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset)), va_CNil())),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset)), va_CNil()))),
    va_CNil()))), va_CCons(va_code_STRglobal(G_USBTD_MAP_MEM(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI), va_op_word_reg(ESI)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI),
    va_op_reg_reg(ECX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))
}

lemma{:timeLimitMultiplier 5} va_lemma_usbtd_set_inputparams(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_set_inputparams(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 3 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires var param_sel:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); (param_sel == G_USBTDs_MAP_ENTRY_InputParam1 || param_sel ==
    G_USBTDs_MAP_ENTRY_InputParam2) || param_sel == G_USBTDs_MAP_ENTRY_InputParam3
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    param_sel:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_input_param:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); usbtd_map_get_inputparam(va_get_globals(va_sM), in_slot,
    param_sel) == new_input_param
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    param_sel:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_input_param:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); ((param_sel == G_USBTDs_MAP_ENTRY_InputParam1 ==> (var vaddr :=
    AddressOfGlobal(G_USBTD_MAP_MEM()) + in_slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset;
    is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) && va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), vaddr, new_input_param))) &&
    (param_sel == G_USBTDs_MAP_ENTRY_InputParam2 ==> (var vaddr :=
    AddressOfGlobal(G_USBTD_MAP_MEM()) + in_slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset;
    is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) && va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), vaddr, new_input_param)))) &&
    (param_sel == G_USBTDs_MAP_ENTRY_InputParam3 ==> (var vaddr :=
    AddressOfGlobal(G_USBTD_MAP_MEM()) + in_slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset;
    is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) && va_get_globals(va_sM) ==
    global_write_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), vaddr, new_input_param)))
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBP, va_sM, va_update_reg(EAX, va_sM, va_update_globals(va_sM,
    va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_usbtd_set_inputparams();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b10, va_s10 := va_lemma_LDRglobaladdr_ToReg(va_b9, va_s9, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s13);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 1938 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b17, va_s17 := va_lemma_MUL_Reg_32BitsResult(va_b13, va_s13, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var input_param_offset;
  ghost var va_s19, va_c19, va_b19 := va_lemma_block(va_b17, va_s17, va_sM);
  ghost var va_cond_c19, va_s20:va_state := va_lemma_ifElse(va_get_ifCond(va_c19),
    va_get_ifTrue(va_c19), va_get_ifFalse(va_c19), va_s17, va_s19);
  if (va_cond_c19)
  {
    ghost var va_b21 := va_get_block(va_get_ifTrue(va_c19));
    ghost var va_b22, va_s22 := va_lemma_ADD(va_b21, va_s20, va_s19, va_op_word_reg(EDI),
      va_const_word(G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset));
    input_param_offset := G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset;
    va_s19 := va_lemma_empty(va_s22, va_s19);
  }
  else
  {
    ghost var va_b24 := va_get_block(va_get_ifFalse(va_c19));
    ghost var va_s25, va_c25, va_b25 := va_lemma_block(va_b24, va_s20, va_s19);
    ghost var va_cond_c25, va_s26:va_state := va_lemma_ifElse(va_get_ifCond(va_c25),
      va_get_ifTrue(va_c25), va_get_ifFalse(va_c25), va_s20, va_s25);
    if (va_cond_c25)
    {
      ghost var va_b27 := va_get_block(va_get_ifTrue(va_c25));
      ghost var va_b28, va_s28 := va_lemma_ADD(va_b27, va_s26, va_s25, va_op_word_reg(EDI),
        va_const_word(G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset));
      input_param_offset := G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset;
      va_s25 := va_lemma_empty(va_s28, va_s25);
    }
    else
    {
      ghost var va_b30 := va_get_block(va_get_ifFalse(va_c25));
      ghost var va_b31, va_s31 := va_lemma_ADD(va_b30, va_s26, va_s25, va_op_word_reg(EDI),
        va_const_word(G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset));
      input_param_offset := G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset;
      va_s25 := va_lemma_empty(va_s31, va_s25);
    }
    va_s19 := va_lemma_empty(va_s25, va_s19);
  }
  Lemma_usbtd_get_inputparams_result_is_gvar_valid_addr(va_get_reg(EDX, va_s19), slot,
    va_get_reg(EDI, va_s19));
  ghost var tmp_addr1 := va_get_reg(EDX, va_s19) + va_get_reg(EDI, va_s19);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s19), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s19));
  ghost var new_this1 := va_s19.(wk_mstate := va_s19.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s19),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s19),
    new_globals1);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s19),
    new_globals1);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s19),
    new_globals1);
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(va_get_globals(va_s19),
    new_globals1, slot, input_param_offset, va_get_reg(ESI, va_s19));
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(va_get_globals(va_s19), new_globals1,
    slot, input_param_offset, va_get_reg(ESI, va_s19));
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(va_get_globals(va_s19), new_globals1,
    slot, input_param_offset, va_get_reg(ESI, va_s19));
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(va_get_globals(va_s19), new_globals1,
    slot, input_param_offset, va_get_reg(ESI, va_s19));
  Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(va_get_globals(va_s19), new_globals1,
    slot, input_param_offset, va_get_reg(ESI, va_s19));
  Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(va_get_globals(va_s19), new_globals1,
    slot, input_param_offset, va_get_reg(ESI, va_s19));
  Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(va_get_globals(va_s19),
    new_globals1, slot, input_param_offset, va_get_reg(ESI, va_s19));
  Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(va_get_globals(va_s19),
    new_globals1, slot, input_param_offset, va_get_reg(ESI, va_s19));
  Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfPIDTypeBusIDWimpDrvSlotIDUSBPDevSlotID_FieldsAreUnchanged(va_get_globals(va_s19),
    new_globals1);
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s19),
    new_globals1);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateInputParamOfUSBTD(va_get_globals(va_s19),
    new_globals1, slot, tmp_addr1, va_get_reg(ESI, va_s19));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s19,
    new_this1);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s19,
    new_this1);
  assert ins_valid_strglobal_word(va_s19.subjects, va_s19.objects, va_s19.id_mappings,
    va_s19.objs_addrs, va_s19.activate_conds, va_get_globals(va_s19), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s19));  // line 1984 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b55, va_s55 := va_lemma_STRglobal(va_b19, va_s19, va_sM, G_USBTD_MAP_MEM(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfMostUSBTDsFieldAndWimpDrvsAndUSBPDevsAreUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_s55));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s55);
  ghost var va_b58, va_s58 := va_lemma_POP_TwoRegs(va_b55, va_s55, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(ECX));
  ghost var va_b59, va_s59 := va_lemma_POP_TwoRegs(va_b58, va_s58, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b60, va_s60 := va_lemma_POP_OneReg(va_b59, va_s59, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s60, va_sM);
}
//--
//-- usbtd_set_id

function method{:opaque} va_code_usbtd_set_id():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_USBTD_MAP_MEM()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_ID_BytesOffset)),
    va_CCons(va_code_STRglobal(G_USBTD_MAP_MEM(), va_op_reg_reg(EDX), va_op_word_reg(EDI),
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_usbtd_set_id(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_set_id(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(slot)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    (((forall i:uint32 :: (usbtd_map_valid_slot_id(i) && i != slot) &&
    usbtd_map_get_idword(va_get_globals(va_s0), i) != USBTD_ID_INVALID ==>
    usbtd_map_get_idword(va_get_globals(va_s0), i) != new_id) && new_id <=
    usbtd_id_counter_read(va_get_globals(va_s0))) && (usbtd_map_get_pid(va_get_globals(va_s0),
    slot) != WS_PartitionID(PID_INVALID) ==> new_id != USBTD_ID_INVALID)) &&
    eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_s0), slot)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    usbtd_map_get_idword(va_get_globals(va_sM), in_slot) == new_id
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var
    vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + in_slot * G_USBTDs_MAP_ENTRY_SZ +
    G_USBTDs_MAP_ENTRY_ID_BytesOffset; is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
    va_get_globals(va_sM) == global_write_word(va_get_globals(va_s0), G_USBTD_MAP_MEM(), vaddr,
    new_id)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_reg(EAX, va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))
{
  reveal_va_code_usbtd_set_id();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ESI));
  ghost var cur_esp := va_get_reg(ESP, va_s8);
  ghost var va_b10, va_s10 := va_lemma_LDRglobaladdr_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    G_USBTD_MAP_MEM());
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s12);
  Lemma_NatMul_Ineq_4var(slot, G_USBTDs_MAP_ENTRY_SZ, USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ);
  assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);  // line 2089 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b16, va_s16 := va_lemma_MUL_Reg_32BitsResult(va_b12, va_s12, va_sM,
    va_op_reg_reg(EDI), va_const_word(G_USBTDs_MAP_ENTRY_SZ));
  ghost var va_b17, va_s17 := va_lemma_ADD(va_b16, va_s16, va_sM, va_op_word_reg(EDI),
    va_const_word(G_USBTDs_MAP_ENTRY_ID_BytesOffset));
  Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset);
  ghost var tmp_addr1 := va_get_reg(EDX, va_s17) + va_get_reg(EDI, va_s17);
  ghost var new_globals1 := global_write_word(va_get_globals(va_s17), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s17));
  ghost var new_this1 := va_s17.(wk_mstate := va_s17.wk_mstate.(globals := new_globals1));
  Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s17),
    new_globals1);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s17),
    new_globals1);
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s17),
    new_globals1);
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s17),
    new_globals1);
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(va_get_globals(va_s17),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, va_get_reg(ESI, va_s17));
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(va_get_globals(va_s17), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, va_get_reg(ESI, va_s17));
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(va_get_globals(va_s17), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, va_get_reg(ESI, va_s17));
  Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(va_get_globals(va_s17), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, va_get_reg(ESI, va_s17));
  Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(va_get_globals(va_s17), new_globals1,
    slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, va_get_reg(ESI, va_s17));
  Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(va_get_globals(va_s17),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, va_get_reg(ESI, va_s17));
  Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(va_get_globals(va_s17),
    new_globals1, slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, va_get_reg(ESI, va_s17));
  Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(va_get_globals(va_s17), new_globals1, slot,
    G_USBTDs_MAP_ENTRY_ID_BytesOffset, va_get_reg(ESI, va_s17));
  Lemma_USBTD_PreserveOtherGvars_WhenModifyingOneSlot(va_get_globals(va_s17), new_globals1, slot,
    G_USBTDs_MAP_ENTRY_ID_BytesOffset, va_get_reg(ESI, va_s17));
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfNewIDOfSlotIsGood(va_s17, new_this1, slot,
    va_get_reg(EDX, va_s17) + va_get_reg(EDI, va_s17), va_get_reg(ESI, va_s17));
  Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s17),
    new_globals1);
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateIDOfEEHCIUnrefedUSBTD(va_get_globals(va_s17),
    new_globals1, slot, tmp_addr1, va_get_reg(ESI, va_s17));
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s17,
    new_this1);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s17,
    new_this1);
  assert ins_valid_strglobal_word(va_s17.subjects, va_s17.objects, va_s17.id_mappings,
    va_s17.objs_addrs, va_s17.activate_conds, va_get_globals(va_s17), G_USBTD_MAP_MEM(), tmp_addr1,
    va_get_reg(ESI, va_s17));  // line 2122 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b41, va_s41 := va_lemma_STRglobal(va_b17, va_s17, va_sM, G_USBTD_MAP_MEM(),
    va_op_reg_reg(EDX), va_op_word_reg(EDI), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfMostUSBTDsFieldAndWimpDrvsAndUSBPDevsAreUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_s41));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s41);
  assert va_get_reg(ESP, va_s41) == cur_esp;  // line 2132 column 5 of file .\dev/usb2/usb_tds_utils.vad
  ghost var va_b45, va_s45 := va_lemma_POP_OneReg(va_b41, va_s41, va_sM, va_op_reg_reg(ESI));
  ghost var va_b46, va_s46 := va_lemma_POP_TwoRegs(va_b45, va_s45, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b47, va_s47 := va_lemma_POP_OneReg(va_b46, va_s46, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s47, va_sM);
}
//--
//-- usbtd_find_empty_slot

function method{:opaque} va_code_usbtd_find_empty_slot(result_slot:va_operand_reg,
  ret:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EDX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX), va_const_word(0)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbtd_get_td_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbtd_get_td_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX),
    va_const_cmp(PID_INVALID)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX),
    va_const_word(FALSE)), va_CNil())), va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX),
    va_const_cmp(USB_TD_ENTRY_NUM - 1)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX),
    va_const_word(FALSE)), va_CNil())), va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX),
    va_const_word(1)), va_CNil()))), va_CNil()))), va_CNil()))))))),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_const_cmp(PID_INVALID)),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(result_slot, va_op_word_reg(EAX)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(result_slot, va_const_word(0)), va_CNil())))),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EDX)), va_CNil())))))))))))
}

lemma{:timeLimitMultiplier 5} va_lemma_usbtd_find_empty_slot(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state, result_slot:va_operand_reg, ret:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_find_empty_slot(result_slot, ret), va_s0, va_sN)
  requires va_is_dst_reg(result_slot, va_s0)
  requires va_is_dst_reg(ret, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires result_slot == Reg1
  requires ret == Reg2
  requires var stack_req_space := 2 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + va_eval_reg(va_sM, result_slot) *
    G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset; (((va_eval_reg(va_sM, ret) == TRUE
    ==> usbtd_map_valid_slot_id(va_eval_reg(va_sM, result_slot))) && (va_eval_reg(va_sM, ret) ==
    TRUE ==> ValidGlobalOffset(G_USBTD_MAP_MEM(), va_eval_reg(va_sM, result_slot) *
    G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset))) && (va_eval_reg(va_sM, ret) ==
    TRUE ==> ((is_valid_addr(vaddr1) && is_valid_vaddr(vaddr1)) &&
    is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), vaddr1)) && PID_INVALID ==
    gvar_read_word_byaddr(va_s0.wk_mstate, G_USBTD_MAP_MEM(), vaddr1))) && (va_eval_reg(va_sM, ret)
    == TRUE ==> usbtd_map_get_pid(va_get_globals(va_s0), va_eval_reg(va_sM, result_slot)) ==
    WS_PartitionID(PID_INVALID))
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(EDX, va_sM, va_update_mem(va_sM, va_update_reg(ESP,
    va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_ok(va_sM,
    va_update_operand_reg(ret, va_sM, va_update_operand_reg(result_slot, va_sM, va_s0))))))))))))
{
  reveal_va_code_usbtd_find_empty_slot();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b5, va_s5 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EDX));
  ghost var begin_state := va_s5;
  ghost var va_b7, va_s7 := va_lemma_MOV_ToReg(va_b5, va_s5, va_sM, va_op_reg_reg(EAX),
    va_const_word(0));
  ghost var va_b8, va_s8 := va_lemma_MOV_ToReg(va_b7, va_s7, va_sM, va_op_reg_reg(EDX),
    va_const_word(TRUE));
  ghost var va_b9, va_s9 := va_lemma_PUSH(va_b8, va_s8, va_sM, va_op_word_reg(EAX));
  ghost var va_b10, va_s10 := va_lemma_usbtd_get_td_pid(va_b9, va_s9, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0);
  ghost var va_b12, va_s12 := va_lemma_POP_VOID(va_b11, va_s11, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var base := AddressOfGlobal(G_USBTD_MAP_MEM());
  Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(va_get_reg(EAX, va_s12),
    G_USBTDs_MAP_ENTRY_PID_BytesOffset);
  ghost var va_s15, va_c15, va_b15 := va_lemma_block(va_b12, va_s12, va_sM);
  ghost var va_n16:int, va_sW16:va_state := va_lemma_while(va_get_whileCond(va_c15),
    va_get_whileBody(va_c15), va_s12, va_s15);
  while (va_n16 > 0)
    invariant va_whileInv(va_get_whileCond(va_c15), va_get_whileBody(va_c15), va_n16, va_sW16,
      va_s15)
    invariant va_get_ok(va_sW16)
    invariant 0 <= va_get_reg(EAX, va_sW16) <= USB_TD_ENTRY_NUM
    invariant va_get_reg(EDX, va_sW16) == TRUE ==> 0 <= va_get_reg(EAX, va_sW16) < USB_TD_ENTRY_NUM
    invariant var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + va_get_reg(EAX, va_sW16) *
      G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset; ((((((((((((va_get_reg(EDX,
      va_sW16) == TRUE ==> is_valid_addr(vaddr1)) && (va_get_reg(EDX, va_sW16) == TRUE ==>
      is_valid_vaddr(vaddr1))) && (va_get_reg(EDX, va_sW16) == TRUE ==>
      is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), vaddr1))) && (va_get_reg(EDX, va_sW16) == TRUE ==>
      ValidGlobalOffset(G_USBTD_MAP_MEM(), va_get_reg(EAX, va_sW16) * G_USBTDs_MAP_ENTRY_SZ +
      G_USBTDs_MAP_ENTRY_PID_BytesOffset))) && (va_get_reg(EDX, va_sW16) != TRUE ==>
      va_get_reg(EBX, va_sW16) == PID_INVALID || va_get_reg(EAX, va_sW16) == USB_TD_ENTRY_NUM - 1))
      && (va_get_reg(EDX, va_sW16) != TRUE && va_get_reg(EBX, va_sW16) == PID_INVALID ==>
      (((va_get_reg(EAX, va_sW16) <= USB_TD_ENTRY_NUM - 1 && is_valid_addr(base + va_get_reg(EAX,
      va_sW16) * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset)) &&
      is_valid_vaddr(base + va_get_reg(EAX, va_sW16) * G_USBTDs_MAP_ENTRY_SZ +
      G_USBTDs_MAP_ENTRY_PID_BytesOffset)) && is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), base +
      va_get_reg(EAX, va_sW16) * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset)) &&
      gvar_read_word_byaddr(va_sW16.wk_mstate, G_USBTD_MAP_MEM(), base + va_get_reg(EAX, va_sW16) *
      G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset) == PID_INVALID)) &&
      va_get_reg(ESP, va_sW16) == va_get_reg(ESP, va_old_s) - 1 * ARCH_WORD_BYTES) &&
      stack_under_sp_is_unchanged(begin_state.wk_mstate.m, va_sW16.wk_mstate.m, va_get_reg(ESP,
      va_sW16))) && va_get_reg(EDI, va_sW16) == va_get_reg(EDI, va_old_s)) && va_get_reg(ESI,
      va_sW16) == va_get_reg(ESI, va_old_s)) && va_get_reg(EBP, va_sW16) == va_get_reg(EBP,
      va_old_s)) && va_get_globals(va_sW16) == va_get_globals(va_old_s)) &&
      state_equal_except_mstate(va_old_s, va_sW16)
    invariant va_state_eq(va_sW16, va_update_reg(EBP, va_sW16, va_update_reg(ESI, va_sW16,
      va_update_reg(EDI, va_sW16, va_update_reg(EDX, va_sW16, va_update_mem(va_sW16,
      va_update_reg(ESP, va_sW16, va_update_reg(EBX, va_sW16, va_update_reg(EAX, va_sW16,
      va_update_ok(va_sW16, va_update_operand_reg(ret, va_sW16, va_update_operand_reg(result_slot,
      va_sW16, va_s0))))))))))))
    decreases USB_TD_ENTRY_NUM - va_get_reg(EAX, va_sW16), va_get_reg(EDX, va_sW16)
  {
    ghost var va_s16:va_state, va_sW17:va_state := va_lemma_whileTrue(va_get_whileCond(va_c15),
      va_get_whileBody(va_c15), va_n16, va_sW16, va_s15);
    ghost var va_b18 := va_get_block(va_get_whileBody(va_c15));
    ghost var va_b19, va_s19 := va_lemma_PUSH(va_b18, va_s16, va_sW17, va_op_word_reg(EAX));
    ghost var va_b20, va_s20 := va_lemma_usbtd_get_td_pid(va_b19, va_s19, va_sW17);
    ghost var va_b21, va_s21 := va_lemma_Load(va_b20, va_s20, va_sW17, va_op_word_reg(EBX),
      va_op_word_reg(ESP), 0);
    ghost var va_b22, va_s22 := va_lemma_POP_VOID(va_b21, va_s21, va_sW17, 1 * ARCH_WORD_BYTES);
    ghost var va_s23, va_c23, va_b23 := va_lemma_block(va_b22, va_s22, va_sW17);
    ghost var va_cond_c23, va_s24:va_state := va_lemma_ifElse(va_get_ifCond(va_c23),
      va_get_ifTrue(va_c23), va_get_ifFalse(va_c23), va_s22, va_s23);
    if (va_cond_c23)
    {
      ghost var va_b25 := va_get_block(va_get_ifTrue(va_c23));
      ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s24, va_s23, va_op_reg_reg(EDX),
        va_const_word(FALSE));
      Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(va_get_reg(EAX, va_s26),
        G_USBTDs_MAP_ENTRY_PID_BytesOffset);
      va_s23 := va_lemma_empty(va_s26, va_s23);
    }
    else
    {
      ghost var va_b28 := va_get_block(va_get_ifFalse(va_c23));
      ghost var va_s29, va_c29, va_b29 := va_lemma_block(va_b28, va_s24, va_s23);
      ghost var va_cond_c29, va_s30:va_state := va_lemma_ifElse(va_get_ifCond(va_c29),
        va_get_ifTrue(va_c29), va_get_ifFalse(va_c29), va_s24, va_s29);
      if (va_cond_c29)
      {
        ghost var va_b31 := va_get_block(va_get_ifTrue(va_c29));
        ghost var va_b32, va_s32 := va_lemma_MOV_ToReg(va_b31, va_s30, va_s29, va_op_reg_reg(EDX),
          va_const_word(FALSE));
        va_s29 := va_lemma_empty(va_s32, va_s29);
      }
      else
      {
        ghost var va_b33 := va_get_block(va_get_ifFalse(va_c29));
        ghost var va_b34, va_s34 := va_lemma_ADD(va_b33, va_s30, va_s29, va_op_word_reg(EAX),
          va_const_word(1));
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(va_get_reg(EAX, va_s34),
          G_USBTDs_MAP_ENTRY_PID_BytesOffset);
        va_s29 := va_lemma_empty(va_s34, va_s29);
      }
      va_s23 := va_lemma_empty(va_s29, va_s23);
    }
    va_sW17 := va_lemma_empty(va_s23, va_sW17);
    va_sW16 := va_sW17;
    va_n16 := va_n16 - 1;
  }
  va_s15 := va_lemma_whileFalse(va_get_whileCond(va_c15), va_get_whileBody(va_c15), va_sW16,
    va_s15);
  ghost var va_s36, va_c36, va_b36 := va_lemma_block(va_b15, va_s15, va_sM);
  ghost var va_cond_c36, va_s37:va_state := va_lemma_ifElse(va_get_ifCond(va_c36),
    va_get_ifTrue(va_c36), va_get_ifFalse(va_c36), va_s15, va_s36);
  if (va_cond_c36)
  {
    ghost var va_b38 := va_get_block(va_get_ifTrue(va_c36));
    assert ValidGlobalOffset(G_USBTD_MAP_MEM(), va_get_reg(EAX, va_s37) * G_USBTDs_MAP_ENTRY_SZ +
      G_USBTDs_MAP_ENTRY_PID_BytesOffset);  // line 2268 column 9 of file .\dev/usb2/usb_tds_utils.vad
    ghost var va_b40, va_s40 := va_lemma_MOV_ToReg(va_b38, va_s37, va_s36, ret,
      va_const_word(TRUE));
    ghost var va_b41, va_s41 := va_lemma_MOV_ToReg(va_b40, va_s40, va_s36, result_slot,
      va_op_word_reg(EAX));
    va_s36 := va_lemma_empty(va_s41, va_s36);
  }
  else
  {
    ghost var va_b42 := va_get_block(va_get_ifFalse(va_c36));
    assert va_get_reg(EAX, va_s37) == USB_TD_ENTRY_NUM - 1;  // line 2275 column 9 of file .\dev/usb2/usb_tds_utils.vad
    ghost var va_b44, va_s44 := va_lemma_MOV_ToReg(va_b42, va_s37, va_s36, ret,
      va_const_word(FALSE));
    ghost var va_b45, va_s45 := va_lemma_MOV_ToReg(va_b44, va_s44, va_s36, result_slot,
      va_const_word(0));
    va_s36 := va_lemma_empty(va_s45, va_s36);
  }
  ghost var va_b46, va_s46 := va_lemma_POP_OneReg(va_b36, va_s36, va_sM, va_op_reg_reg(EDX));
  va_sM := va_lemma_empty(va_s46, va_sM);
}
//--
//-- usbtd_find_slot_in_partition

function method{:opaque} va_code_usbtd_find_slot_in_partition():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbtd_get_td_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil())))),
    va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbtd_get_td_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(EDI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(USB_TD_ENTRY_NUM - 1)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil()))),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(FALSE)), va_CNil()))))),
    va_CNil()))), va_CNil()))))))), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX),
    va_op_cmp_reg(EDI)), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EAX)), va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_const_word(USBTD_SlotID_INVALID)), va_CNil())))),
    va_CCons(va_code_POP_Reg1ToReg6(), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)),
    va_CNil()))))))))))))))))
}

lemma{:timeLimitMultiplier 5} va_lemma_usbtd_find_slot_in_partition(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_find_slot_in_partition(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    result_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((ret == TRUE ==>
    usbtd_map_valid_slot_id(result_slot)) && (ret == TRUE ==>
    usbtd_map_get_pid(va_get_globals(va_s0), result_slot) == WS_PartitionID(pid))) && (ret == FALSE
    ==> (forall i:word :: usbtd_map_valid_slot_id(i) ==> usbtd_map_get_pid(va_get_globals(va_s0),
    i) != WS_PartitionID(pid)))
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
    stack_retval_space) && va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_usbtd_find_slot_in_partition();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b9, va_s9 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var begin_state := va_s9;
  ghost var orig_ebp := va_get_reg(EBP, va_s9);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var in_pid := va_get_reg(EDI, va_s12);
  ghost var va_b14, va_s14 := va_lemma_MOV_ToReg(va_b12, va_s12, va_sM, va_op_reg_reg(EAX),
    va_const_word(0));
  ghost var va_b15, va_s15 := va_lemma_MOV_ToReg(va_b14, va_s14, va_sM, va_op_reg_reg(EDX),
    va_const_word(TRUE));
  ghost var va_b16, va_s16 := va_lemma_PUSH(va_b15, va_s15, va_sM, va_op_word_reg(EAX));
  ghost var va_b17, va_s17 := va_lemma_usbtd_get_td_pid(va_b16, va_s16, va_sM);
  ghost var va_b18, va_s18 := va_lemma_Load(va_b17, va_s17, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0);
  ghost var va_b19, va_s19 := va_lemma_POP_VOID(va_b18, va_s18, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_s20, va_c20, va_b20 := va_lemma_block(va_b19, va_s19, va_sM);
  ghost var va_cond_c20, va_s21:va_state := va_lemma_ifElse(va_get_ifCond(va_c20),
    va_get_ifTrue(va_c20), va_get_ifFalse(va_c20), va_s19, va_s20);
  if (va_cond_c20)
  {
    ghost var va_b22 := va_get_block(va_get_ifTrue(va_c20));
    ghost var va_b23, va_s23 := va_lemma_MOV_ToReg(va_b22, va_s21, va_s20, va_op_reg_reg(EDX),
      va_const_word(FALSE));
    ghost var va_b24, va_s24 := va_lemma_MOV_ToReg(va_b23, va_s23, va_s20, va_op_reg_reg(ECX),
      va_const_word(TRUE));
    va_s20 := va_lemma_empty(va_s24, va_s20);
  }
  else
  {
    ghost var va_b25 := va_get_block(va_get_ifFalse(va_c20));
    ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s21, va_s20, va_op_reg_reg(EDX),
      va_const_word(TRUE));
    ghost var va_b27, va_s27 := va_lemma_MOV_ToReg(va_b26, va_s26, va_s20, va_op_reg_reg(ECX),
      va_const_word(FALSE));
    va_s20 := va_lemma_empty(va_s27, va_s20);
  }
  ghost var va_s28, va_c28, va_b28 := va_lemma_block(va_b20, va_s20, va_sM);
  ghost var va_n29:int, va_sW29:va_state := va_lemma_while(va_get_whileCond(va_c28),
    va_get_whileBody(va_c28), va_s20, va_s28);
  while (va_n29 > 0)
    invariant va_whileInv(va_get_whileCond(va_c28), va_get_whileBody(va_c28), va_n29, va_sW29,
      va_s28)
    invariant va_get_ok(va_sW29)
    invariant 0 <= va_get_reg(EAX, va_sW29) <= USB_TD_ENTRY_NUM
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> 0 <= va_get_reg(EAX, va_sW29) < USB_TD_ENTRY_NUM
    invariant va_get_reg(EDX, va_sW29) == TRUE ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(EBX, va_sW29) != in_pid ==> va_get_reg(ECX, va_sW29) == FALSE
    invariant va_get_reg(ECX, va_sW29) == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX,
      va_sW29) && usbtd_map_valid_slot_id(j) ==> usbtd_map_get_pid(va_get_globals(va_old_s), j) !=
      WS_PartitionID(in_pid))
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(ECX, va_sW29) == FALSE ==> (forall
      j:uint32 :: usbtd_map_valid_slot_id(j) ==> usbtd_map_get_pid(va_get_globals(va_old_s), j) !=
      WS_PartitionID(in_pid))
    invariant va_get_reg(EDX, va_sW29) != TRUE ==> va_get_reg(EBX, va_sW29) == in_pid ||
      va_get_reg(EAX, va_sW29) == USB_TD_ENTRY_NUM - 1
    invariant va_get_reg(EDX, va_sW29) != TRUE && va_get_reg(EBX, va_sW29) == in_pid ==>
      usbtd_map_valid_slot_id(va_get_reg(EAX, va_sW29)) &&
      usbtd_map_get_pid(va_get_globals(va_old_s), va_get_reg(EAX, va_sW29)) ==
      WS_PartitionID(in_pid)
    invariant va_get_reg(ESP, va_sW29) == va_get_reg(ESP, va_old_s) - 7 * ARCH_WORD_BYTES
    invariant stack_under_sp_is_unchanged(begin_state.wk_mstate.m, va_sW29.wk_mstate.m,
      va_get_reg(ESP, va_sW29))
    invariant va_get_reg(ESI, va_sW29) == va_get_reg(ESI, va_old_s)
    invariant va_get_reg(EBP, va_sW29) == orig_ebp
    invariant va_get_reg(EDI, va_sW29) == in_pid
    invariant va_get_globals(va_sW29) == va_get_globals(va_old_s)
    invariant state_equal_except_mstate(va_old_s, va_sW29)
    invariant va_state_eq(va_sW29, va_update_reg(EDI, va_sW29, va_update_reg(ESI, va_sW29,
      va_update_reg(EDX, va_sW29, va_update_reg(ECX, va_sW29, va_update_reg(EBX, va_sW29,
      va_update_reg(EAX, va_sW29, va_update_mem(va_sW29, va_update_reg(EBP, va_sW29,
      va_update_reg(ESP, va_sW29, va_update_ok(va_sW29, va_s0)))))))))))
    decreases USB_TD_ENTRY_NUM - va_get_reg(EAX, va_sW29), va_get_reg(EDX, va_sW29)
  {
    ghost var va_s29:va_state, va_sW30:va_state := va_lemma_whileTrue(va_get_whileCond(va_c28),
      va_get_whileBody(va_c28), va_n29, va_sW29, va_s28);
    ghost var va_b31 := va_get_block(va_get_whileBody(va_c28));
    ghost var va_b32, va_s32 := va_lemma_PUSH(va_b31, va_s29, va_sW30, va_op_word_reg(EAX));
    ghost var va_b33, va_s33 := va_lemma_usbtd_get_td_pid(va_b32, va_s32, va_sW30);
    ghost var va_b34, va_s34 := va_lemma_Load(va_b33, va_s33, va_sW30, va_op_word_reg(EBX),
      va_op_word_reg(ESP), 0);
    ghost var va_b35, va_s35 := va_lemma_POP_VOID(va_b34, va_s34, va_sW30, 1 * ARCH_WORD_BYTES);
    ghost var va_s36, va_c36, va_b36 := va_lemma_block(va_b35, va_s35, va_sW30);
    ghost var va_cond_c36, va_s37:va_state := va_lemma_ifElse(va_get_ifCond(va_c36),
      va_get_ifTrue(va_c36), va_get_ifFalse(va_c36), va_s35, va_s36);
    if (va_cond_c36)
    {
      ghost var va_b38 := va_get_block(va_get_ifTrue(va_c36));
      ghost var va_b39, va_s39 := va_lemma_MOV_ToReg(va_b38, va_s37, va_s36, va_op_reg_reg(EDX),
        va_const_word(FALSE));
      ghost var va_b40, va_s40 := va_lemma_MOV_ToReg(va_b39, va_s39, va_s36, va_op_reg_reg(ECX),
        va_const_word(TRUE));
      va_s36 := va_lemma_empty(va_s40, va_s36);
    }
    else
    {
      ghost var va_b41 := va_get_block(va_get_ifFalse(va_c36));
      ghost var va_s42, va_c42, va_b42 := va_lemma_block(va_b41, va_s37, va_s36);
      ghost var va_cond_c42, va_s43:va_state := va_lemma_ifElse(va_get_ifCond(va_c42),
        va_get_ifTrue(va_c42), va_get_ifFalse(va_c42), va_s37, va_s42);
      if (va_cond_c42)
      {
        ghost var va_b44 := va_get_block(va_get_ifTrue(va_c42));
        ghost var va_b45, va_s45 := va_lemma_MOV_ToReg(va_b44, va_s43, va_s42, va_op_reg_reg(EDX),
          va_const_word(FALSE));
        ghost var va_b46, va_s46 := va_lemma_MOV_ToReg(va_b45, va_s45, va_s42, va_op_reg_reg(ECX),
          va_const_word(FALSE));
        va_s42 := va_lemma_empty(va_s46, va_s42);
      }
      else
      {
        ghost var va_b47 := va_get_block(va_get_ifFalse(va_c42));
        ghost var va_b48, va_s48 := va_lemma_ADD(va_b47, va_s43, va_s42, va_op_word_reg(EAX),
          va_const_word(1));
        ghost var va_b49, va_s49 := va_lemma_MOV_ToReg(va_b48, va_s48, va_s42, va_op_reg_reg(EDX),
          va_const_word(TRUE));
        ghost var va_b50, va_s50 := va_lemma_MOV_ToReg(va_b49, va_s49, va_s42, va_op_reg_reg(ECX),
          va_const_word(FALSE));
        va_s42 := va_lemma_empty(va_s50, va_s42);
      }
      va_s36 := va_lemma_empty(va_s42, va_s36);
    }
    va_sW30 := va_lemma_empty(va_s36, va_sW30);
    va_sW29 := va_sW30;
    va_n29 := va_n29 - 1;
  }
  va_s28 := va_lemma_whileFalse(va_get_whileCond(va_c28), va_get_whileBody(va_c28), va_sW29,
    va_s28);
  ghost var va_s51, va_c51, va_b51 := va_lemma_block(va_b28, va_s28, va_sM);
  ghost var va_cond_c51, va_s52:va_state := va_lemma_ifElse(va_get_ifCond(va_c51),
    va_get_ifTrue(va_c51), va_get_ifFalse(va_c51), va_s28, va_s51);
  if (va_cond_c51)
  {
    ghost var va_b53 := va_get_block(va_get_ifTrue(va_c51));
    ghost var va_b54, va_s54 := va_lemma_Store(va_b53, va_s52, va_s51, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    ghost var va_b55, va_s55 := va_lemma_Store(va_b54, va_s54, va_s51, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_op_word_reg(EAX));
    va_s51 := va_lemma_empty(va_s55, va_s51);
  }
  else
  {
    ghost var va_b56 := va_get_block(va_get_ifFalse(va_c51));
    assert va_get_reg(EAX, va_s52) == USB_TD_ENTRY_NUM - 1;  // line 2436 column 9 of file .\dev/usb2/usb_tds_utils.vad
    assert va_get_reg(ECX, va_s52) == FALSE;  // line 2437 column 9 of file .\dev/usb2/usb_tds_utils.vad
    ghost var va_b59, va_s59 := va_lemma_Store(va_b56, va_s52, va_s51, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s59, va_s51, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(USBTD_SlotID_INVALID));
    va_s51 := va_lemma_empty(va_s60, va_s51);
  }
  ghost var va_b61, va_s61 := va_lemma_POP_Reg1ToReg6(va_b51, va_s51, va_sM);
  ghost var va_b62, va_s62 := va_lemma_POP_OneReg(va_b61, va_s61, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s62, va_sM);
}
//--
//-- usbtd_id_generate

function method{:opaque} va_code_usbtd_id_generate(ret:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDI), G_USBTD_ID_Counter()),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_USBTD_ID_Counter(), va_op_reg_reg(EDI),
    va_const_word(0)), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(USBTD_ID_MAX -
    1)), va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(USBTD_ID_INVALID)), va_CNil())),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(USBTD_ID_MAX)),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(USBTD_ID_INVALID)), va_CNil())),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(ESI), va_const_word(1)),
    va_CCons(va_code_STRglobal(G_USBTD_ID_Counter(), va_op_reg_reg(EDI), va_const_word(0),
    va_op_word_reg(ESI)), va_CCons(va_code_MOV_ToReg(ret, va_op_word_reg(ESI)), va_CNil()))))),
    va_CNil()))), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CNil()))))))
}

lemma va_lemma_usbtd_id_generate(va_b0:va_codes, va_s0:va_state, va_sN:va_state, ret:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_id_generate(ret), va_s0, va_sN)
  requires va_is_dst_reg(ret, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires ret == Reg1
  requires IsAddrInStack(va_get_reg(ESP, va_s0) - 2 * ARCH_WORD_BYTES)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  globals_other_gvar_unchanged(va_get_globals(va_s0), va_get_globals(va_sM),
    G_USBTD_ID_Counter())
  ensures  va_eval_reg(va_sM, ret) != USBTD_ID_INVALID ==> (forall i:word ::
    usbtd_map_valid_slot_id(i) ==> usbtd_map_get_idword(va_get_globals(va_sM), i) <
    va_eval_reg(va_sM, ret) || usbtd_map_get_idword(va_get_globals(va_sM), i) == USBTD_ID_INVALID)
  ensures  va_eval_reg(va_sM, ret) != USBTD_ID_INVALID ==> va_eval_reg(va_sM, ret) ==
    usbtd_id_counter_read(va_get_globals(va_sM))
  ensures  va_eval_reg(va_sM, ret) == USBTD_ID_INVALID ==> va_get_globals(va_sM) ==
    va_get_globals(va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_mem(va_sM, va_update_globals(va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM,
    va_update_operand_reg(ret, va_sM, va_s0))))))))
{
  reveal_va_code_usbtd_id_generate();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b4, va_s4 := va_lemma_PUSH_TwoRegs(va_b1, va_s0, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b5, va_s5 := va_lemma_LDRglobaladdr_ToReg(va_b4, va_s4, va_sM, va_op_reg_reg(EDI),
    G_USBTD_ID_Counter());
  ghost var va_b6, va_s6 := va_lemma_LDRglobal(va_b5, va_s5, va_sM, va_op_word_reg(ESI),
    G_USBTD_ID_Counter(), va_op_reg_reg(EDI), va_const_word(0));
  ghost var va_s7, va_c7, va_b7 := va_lemma_block(va_b6, va_s6, va_sM);
  ghost var va_cond_c7, va_s8:va_state := va_lemma_ifElse(va_get_ifCond(va_c7),
    va_get_ifTrue(va_c7), va_get_ifFalse(va_c7), va_s6, va_s7);
  if (va_cond_c7)
  {
    ghost var va_b9 := va_get_block(va_get_ifTrue(va_c7));
    ghost var va_b10, va_s10 := va_lemma_MOV_ToReg(va_b9, va_s8, va_s7, ret,
      va_const_word(USBTD_ID_INVALID));
    va_s7 := va_lemma_empty(va_s10, va_s7);
  }
  else
  {
    ghost var va_b11 := va_get_block(va_get_ifFalse(va_c7));
    ghost var va_s12, va_c12, va_b12 := va_lemma_block(va_b11, va_s8, va_s7);
    ghost var va_cond_c12, va_s13:va_state := va_lemma_ifElse(va_get_ifCond(va_c12),
      va_get_ifTrue(va_c12), va_get_ifFalse(va_c12), va_s8, va_s12);
    if (va_cond_c12)
    {
      ghost var va_b14 := va_get_block(va_get_ifTrue(va_c12));
      ghost var va_b15, va_s15 := va_lemma_MOV_ToReg(va_b14, va_s13, va_s12, ret,
        va_const_word(USBTD_ID_INVALID));
      va_s12 := va_lemma_empty(va_s15, va_s12);
    }
    else
    {
      ghost var va_b16 := va_get_block(va_get_ifFalse(va_c12));
      ghost var va_b17, va_s17 := va_lemma_ADD(va_b16, va_s13, va_s12, va_op_word_reg(ESI),
        va_const_word(1));
      ghost var new_globals := global_write_word(va_get_globals(va_s17), G_USBTD_ID_Counter(),
        va_get_reg(EDI, va_s17), va_get_reg(ESI, va_s17));
      ghost var new_this := va_s17.(wk_mstate := va_s17.wk_mstate.(globals := new_globals));
      Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s17),
        new_globals);
      Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s17),
        new_globals);
      assert global_read_fullval(new_globals, G_WimpDrvs_Info()) ==
        global_read_fullval(va_get_globals(va_s17), G_WimpDrvs_Info());  // line 2518 column 13 of file .\dev/usb2/usb_tds_utils.vad
      Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s17),
        new_globals);
      Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s17),
        new_globals);
      Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s17),
        new_globals);
      Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s17),
        new_globals);
      Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGUSBTDIDCounterIncreased(va_get_globals(va_s17),
        new_globals);
      Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s17),
        new_globals);
      Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s17),
        new_globals);
      Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s17,
        new_this);
      Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s17,
        new_this);
      assert ins_valid_strglobal_word(va_s17.subjects, va_s17.objects, va_s17.id_mappings,
        va_s17.objs_addrs, va_s17.activate_conds, va_get_globals(va_s17), G_USBTD_ID_Counter(),
        va_get_reg(EDI, va_s17), va_get_reg(ESI, va_s17));  // line 2530 column 13 of file .\dev/usb2/usb_tds_utils.vad
      ghost var va_b33, va_s33 := va_lemma_STRglobal(va_b17, va_s17, va_s12, G_USBTD_ID_Counter(),
        va_op_reg_reg(EDI), va_const_word(0), va_op_word_reg(ESI));
      Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(va_get_globals(va_old_s),
        va_get_globals(va_s33));
      Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
        va_s33);
      Lemma_usbtd_id_generate_ProveProperty2(va_get_globals(va_old_s), va_get_globals(va_s33));
      ghost var va_b37, va_s37 := va_lemma_MOV_ToReg(va_b33, va_s33, va_s12, ret,
        va_op_word_reg(ESI));
      va_s12 := va_lemma_empty(va_s37, va_s12);
    }
    va_s7 := va_lemma_empty(va_s12, va_s7);
  }
  ghost var va_b38, va_s38 := va_lemma_POP_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  va_sM := va_lemma_empty(va_s38, va_sM);
}
//--
lemma Lemma_usbtd_id_generate_ProveProperty2(old_globals:globalsmap, new_globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(old_globals)

    requires globals_other_gvar_unchanged(old_globals, new_globals, G_USBTD_ID_Counter())
    requires usbtd_id_counter_read(old_globals) + 1 == usbtd_id_counter_read(new_globals)

    ensures forall i :: usbtd_map_valid_slot_id(i)
                ==> (usbtd_map_get_idword(new_globals, i) < usbtd_id_counter_read(new_globals) ||
                     usbtd_map_get_idword(new_globals, i) == USBTD_ID_INVALID)
{
    forall i | usbtd_map_valid_slot_id(i)
        ensures usbtd_map_get_idword(new_globals, i) < usbtd_id_counter_read(new_globals) ||
                usbtd_map_get_idword(new_globals, i) == USBTD_ID_INVALID
    {
        assert usbtd_map_get_idword(new_globals, i) == usbtd_map_get_idword(old_globals, i);
        assert usbtd_id_counter_read(old_globals) < usbtd_id_counter_read(new_globals);

        assert usbtd_slot_valid_id(old_globals, i);
    }
}
