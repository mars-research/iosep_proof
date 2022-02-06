include "../../../ins/x86/ins_wrapper.gen.dfy"
include "../usb_tds_utils.gen.dfy"
include "../../../partition_id_ops.gen.dfy"
include "../eehci_info.gen.dfy"
include "..\\usb_tds_utils.i.dfy"
include "usb_tds_ops.dafny21.gen.dfy"
//-- _usbtd_find_referencing_secure_slot

function method{:opaque} va_code__usbtd_find_referencing_secure_slot():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(ESI)),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_CALL_USBTD_IsRefTargetUSBTD(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(ESI)),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbtd_get_flags(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_TestBit(va_op_word_reg(EDI),
    USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(FALSE)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)), va_CNil()))),
    va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)),
    va_CNil()))), va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(ESI)),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_CALL_USBTD_IsRefTargetUSBTD(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(ESI)),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbtd_get_flags(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_TestBit(va_op_word_reg(EDI),
    USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(FALSE)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(USB_TD_ENTRY_NUM - 1)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)), va_CNil())))),
    va_CNil()))), va_CNil())), va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX),
    va_const_cmp(USB_TD_ENTRY_NUM - 1)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI),
    va_const_word(FALSE)), va_CNil())), va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX),
    va_const_word(1)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)),
    va_CNil())))), va_CNil()))), va_CNil()))))))))))))))))),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES, va_op_word_reg(EAX)),
    va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(USBTD_SlotID_INVALID)), va_CNil())))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(USBTD_SlotID_INVALID)), va_CNil())))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))))))))))))
}

lemma{:timeLimitMultiplier 100} va_lemma__usbtd_find_referencing_secure_slot(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbtd_find_referencing_secure_slot(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 9 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ +
    FFI_USBTD_IsRefTargetUSBTD_StackParamsWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var target_td_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var src_slot:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); (((ret == TRUE ==>
    usbtd_map_valid_slot_id(src_slot)) && (ret == TRUE ==>
    usbtd_is_slot_ref_target_slot(va_get_globals(va_s0), src_slot, target_td_slot))) && (ret ==
    TRUE ==> TestBit(usbtd_map_get_flags(va_get_globals(va_s0), src_slot),
    USBTD_SLOT_FLAG_SlotSecure_Bit))) && (ret != TRUE ==> (forall i:uint32 ::
    usbtd_map_valid_slot_id(i) ==> !(usbtd_is_slot_ref_target_slot(va_get_globals(va_s0), i,
    target_td_slot) && TestBit(usbtd_map_get_flags(va_get_globals(va_s0), i),
    USBTD_SLOT_FLAG_SlotSecure_Bit))))
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
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code__usbtd_find_referencing_secure_slot();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_p_ffi_usbtd_is_ref_target_usbtd_retval();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b11, va_s11 := va_lemma_PUSH_Reg1ToReg6(va_b4, va_s4, va_sM);
  ghost var begin_state := va_s11;
  ghost var orig_ebp := va_get_reg(EBP, va_s11);
  ghost var va_b14, va_s14 := va_lemma_MOV_ToReg(va_b11, va_s11, va_sM, va_op_reg_reg(EAX),
    va_const_word(0));
  ghost var va_b15, va_s15 := va_lemma_MOV_ToReg(va_b14, va_s14, va_sM, va_op_reg_reg(ESI),
    va_const_word(TRUE));
  ghost var va_b16, va_s16 := va_lemma_MOV_ToReg(va_b15, va_s15, va_sM, va_op_reg_reg(ECX),
    va_const_word(TRUE));
  ghost var va_b17, va_s17 := va_lemma_MOV_ToReg(va_b16, va_s16, va_sM, va_op_reg_reg(EDX),
    va_const_word(TRUE));
  ghost var va_b18, va_s18 := va_lemma_Load(va_b17, va_s17, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var in_target_td_slot := va_get_reg(EDI, va_s18);
  ghost var va_b20, va_s20 := va_lemma_PUSH_TwoRegs(va_b18, va_s18, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(ESI));
  ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s20, va_sM, va_op_word_reg(EDI));
  ghost var va_b22, va_s22 := va_lemma_PUSH(va_b21, va_s21, va_sM, va_op_word_reg(EAX));
  ghost var va_b23, va_s23 := va_lemma_CALL_USBTD_IsRefTargetUSBTD(va_b22, va_s22, va_sM);
  ghost var va_b24, va_s24 := va_lemma_Load(va_b23, va_s23, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0);
  ghost var va_b25, va_s25 := va_lemma_POP_VOID(va_b24, va_s24, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_b26, va_s26 := va_lemma_POP_TwoRegs(va_b25, va_s25, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(ESI));
  ghost var va_b27, va_s27 := va_lemma_PUSH(va_b26, va_s26, va_sM, va_op_word_reg(EAX));
  ghost var va_b28, va_s28 := va_lemma_usbtd_get_flags(va_b27, va_s27, va_sM);
  ghost var va_b29, va_s29 := va_lemma_Load(va_b28, va_s28, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0);
  ghost var va_b30, va_s30 := va_lemma_POP_VOID(va_b29, va_s29, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b31, va_s31 := va_lemma_TestBit(va_b30, va_s30, va_sM, va_op_word_reg(EDI),
    USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX));
  ghost var va_b32, va_s32 := va_lemma_MOV_ToReg(va_b31, va_s31, va_sM, va_op_reg_reg(EBX),
    va_const_word(FALSE));
  ghost var va_s33, va_c33, va_b33 := va_lemma_block(va_b32, va_s32, va_sM);
  ghost var va_cond_c33, va_s34:va_state := va_lemma_ifElse(va_get_ifCond(va_c33),
    va_get_ifTrue(va_c33), va_get_ifFalse(va_c33), va_s32, va_s33);
  if (va_cond_c33)
  {
    ghost var va_b35 := va_get_block(va_get_ifTrue(va_c33));
    ghost var va_s36, va_c36, va_b36 := va_lemma_block(va_b35, va_s34, va_s33);
    ghost var va_cond_c36, va_s37:va_state := va_lemma_ifElse(va_get_ifCond(va_c36),
      va_get_ifTrue(va_c36), va_get_ifFalse(va_c36), va_s34, va_s36);
    if (va_cond_c36)
    {
      ghost var va_b38 := va_get_block(va_get_ifTrue(va_c36));
      ghost var va_b39, va_s39 := va_lemma_MOV_ToReg(va_b38, va_s37, va_s36, va_op_reg_reg(ESI),
        va_const_word(FALSE));
      ghost var va_b40, va_s40 := va_lemma_MOV_ToReg(va_b39, va_s39, va_s36, va_op_reg_reg(EBX),
        va_const_word(TRUE));
      va_s36 := va_lemma_empty(va_s40, va_s36);
    }
    else
    {
      ghost var va_b41 := va_get_block(va_get_ifFalse(va_c36));
      ghost var va_b42, va_s42 := va_lemma_MOV_ToReg(va_b41, va_s37, va_s36, va_op_reg_reg(ESI),
        va_const_word(TRUE));
      va_s36 := va_lemma_empty(va_s42, va_s36);
    }
    va_s33 := va_lemma_empty(va_s36, va_s33);
  }
  else
  {
    ghost var va_b43 := va_get_block(va_get_ifFalse(va_c33));
    ghost var va_b44, va_s44 := va_lemma_MOV_ToReg(va_b43, va_s34, va_s33, va_op_reg_reg(ESI),
      va_const_word(TRUE));
    va_s33 := va_lemma_empty(va_s44, va_s33);
  }
  ghost var va_s45, va_c45, va_b45 := va_lemma_block(va_b33, va_s33, va_sM);
  ghost var va_n46:int, va_sW46:va_state := va_lemma_while(va_get_whileCond(va_c45),
    va_get_whileBody(va_c45), va_s33, va_s45);
  while (va_n46 > 0)
    invariant va_whileInv(va_get_whileCond(va_c45), va_get_whileBody(va_c45), va_n46, va_sW46,
      va_s45)
    invariant va_get_ok(va_sW46)
    invariant 0 <= va_get_reg(EAX, va_sW46) <= USB_TD_ENTRY_NUM
    invariant va_get_reg(ESI, va_sW46) == TRUE ==> 0 <= va_get_reg(EAX, va_sW46) < USB_TD_ENTRY_NUM
    invariant va_get_reg(EBX, va_sW46) == TRUE || va_get_reg(EBX, va_sW46) == FALSE
    invariant va_get_reg(ESI, va_sW46) == TRUE ==> va_get_reg(EBX, va_sW46) == FALSE
    invariant va_get_reg(EBX, va_sW46) == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX,
      va_sW46) && usbtd_map_valid_slot_id(j) ==>
      !(usbtd_is_slot_ref_target_slot(va_get_globals(va_sW46), j, in_target_td_slot) &&
      TestBit(usbtd_map_get_flags(va_get_globals(va_sW46), j), USBTD_SLOT_FLAG_SlotSecure_Bit)))
    invariant va_get_reg(ESI, va_sW46) != TRUE && va_get_reg(EBX, va_sW46) == FALSE ==> (forall
      j:uint32 :: usbtd_map_valid_slot_id(j) ==>
      !(usbtd_is_slot_ref_target_slot(va_get_globals(va_sW46), j, in_target_td_slot) &&
      TestBit(usbtd_map_get_flags(va_get_globals(va_sW46), j), USBTD_SLOT_FLAG_SlotSecure_Bit)))
    invariant va_get_reg(ESI, va_sW46) != TRUE ==> (va_get_reg(ECX, va_sW46) == TRUE &&
      va_get_reg(EDX, va_sW46) == TRUE <==> va_get_reg(EBX, va_sW46) == TRUE)
    invariant va_get_reg(ESI, va_sW46) != TRUE ==> (va_get_reg(ECX, va_sW46) == TRUE &&
      va_get_reg(EDX, va_sW46) == TRUE) || va_get_reg(EAX, va_sW46) == USB_TD_ENTRY_NUM - 1
    invariant va_get_reg(ESI, va_sW46) != TRUE && (va_get_reg(ECX, va_sW46) == TRUE &&
      va_get_reg(EDX, va_sW46) == TRUE) ==> (usbtd_map_valid_slot_id(va_get_reg(EAX, va_sW46)) &&
      TestBit(usbtd_map_get_flags(va_get_globals(va_sW46), va_get_reg(EAX, va_sW46)),
      USBTD_SLOT_FLAG_SlotSecure_Bit)) && usbtd_is_slot_ref_target_slot(va_get_globals(va_sW46),
      va_get_reg(EAX, va_sW46), in_target_td_slot)
    invariant va_get_reg(ESP, va_sW46) == va_get_reg(ESP, va_old_s) - 7 * ARCH_WORD_BYTES
    invariant stack_under_sp_is_unchanged(begin_state.wk_mstate.m, va_sW46.wk_mstate.m,
      va_get_reg(ESP, va_sW46))
    invariant va_get_globals(va_sW46) == va_get_globals(va_old_s)
    invariant va_get_reg(EBP, va_sW46) == orig_ebp
    invariant state_equal_except_mstate(va_old_s, va_sW46)
    invariant va_state_eq(va_sW46, va_update_reg(EDX, va_sW46, va_update_reg(ECX, va_sW46,
      va_update_reg(EBX, va_sW46, va_update_reg(EAX, va_sW46, va_update_reg(EDI, va_sW46,
      va_update_reg(ESI, va_sW46, va_update_mem(va_sW46, va_update_reg(ESP, va_sW46,
      va_update_reg(EBP, va_sW46, va_update_ok(va_sW46, va_s0)))))))))))
    decreases USB_TD_ENTRY_NUM - va_get_reg(EAX, va_sW46), va_get_reg(ESI, va_sW46)
  {
    ghost var va_s46:va_state, va_sW47:va_state := va_lemma_whileTrue(va_get_whileCond(va_c45),
      va_get_whileBody(va_c45), va_n46, va_sW46, va_s45);
    ghost var va_b48 := va_get_block(va_get_whileBody(va_c45));
    ghost var old_this := va_s46;
    ghost var va_b50, va_s50 := va_lemma_Load(va_b48, va_s46, va_sW47, va_op_word_reg(EDI),
      va_op_word_reg(EBP), ARCH_WORD_BYTES);
    ghost var va_b51, va_s51 := va_lemma_PUSH_TwoRegs(va_b50, va_s50, va_sW47, va_op_reg_reg(EAX),
      va_op_reg_reg(ESI));
    ghost var va_b52, va_s52 := va_lemma_PUSH(va_b51, va_s51, va_sW47, va_op_word_reg(EDI));
    ghost var va_b53, va_s53 := va_lemma_PUSH(va_b52, va_s52, va_sW47, va_op_word_reg(EAX));
    ghost var va_b54, va_s54 := va_lemma_CALL_USBTD_IsRefTargetUSBTD(va_b53, va_s53, va_sW47);
    ghost var va_b55, va_s55 := va_lemma_Load(va_b54, va_s54, va_sW47, va_op_word_reg(ECX),
      va_op_word_reg(ESP), 0);
    ghost var va_b56, va_s56 := va_lemma_POP_VOID(va_b55, va_s55, va_sW47, 2 * ARCH_WORD_BYTES);
    ghost var va_b57, va_s57 := va_lemma_POP_TwoRegs(va_b56, va_s56, va_sW47, va_op_reg_reg(EAX),
      va_op_reg_reg(ESI));
    ghost var va_b58, va_s58 := va_lemma_PUSH(va_b57, va_s57, va_sW47, va_op_word_reg(EAX));
    ghost var va_b59, va_s59 := va_lemma_usbtd_get_flags(va_b58, va_s58, va_sW47);
    ghost var va_b60, va_s60 := va_lemma_Load(va_b59, va_s59, va_sW47, va_op_word_reg(EDI),
      va_op_word_reg(ESP), 0);
    ghost var va_b61, va_s61 := va_lemma_POP_VOID(va_b60, va_s60, va_sW47, 1 * ARCH_WORD_BYTES);
    ghost var va_b62, va_s62 := va_lemma_TestBit(va_b61, va_s61, va_sW47, va_op_word_reg(EDI),
      USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX));
    ghost var va_b63, va_s63 := va_lemma_MOV_ToReg(va_b62, va_s62, va_sW47, va_op_reg_reg(EBX),
      va_const_word(FALSE));
    ghost var cur_i := va_get_reg(EAX, va_s63);
    ghost var va_s65, va_c65, va_b65 := va_lemma_block(va_b63, va_s63, va_sW47);
    ghost var va_cond_c65, va_s66:va_state := va_lemma_ifElse(va_get_ifCond(va_c65),
      va_get_ifTrue(va_c65), va_get_ifFalse(va_c65), va_s63, va_s65);
    if (va_cond_c65)
    {
      ghost var va_b67 := va_get_block(va_get_ifTrue(va_c65));
      assert usbtd_is_slot_ref_target_slot(va_get_globals(va_s66), va_get_reg(EAX, va_s66),
        in_target_td_slot);  // line 178 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      ghost var va_s69, va_c69, va_b69 := va_lemma_block(va_b67, va_s66, va_s65);
      ghost var va_cond_c69, va_s70:va_state := va_lemma_ifElse(va_get_ifCond(va_c69),
        va_get_ifTrue(va_c69), va_get_ifFalse(va_c69), va_s66, va_s69);
      if (va_cond_c69)
      {
        ghost var va_b71 := va_get_block(va_get_ifTrue(va_c69));
        ghost var va_b72, va_s72 := va_lemma_MOV_ToReg(va_b71, va_s70, va_s69, va_op_reg_reg(ESI),
          va_const_word(FALSE));
        ghost var va_b73, va_s73 := va_lemma_MOV_ToReg(va_b72, va_s72, va_s69, va_op_reg_reg(EBX),
          va_const_word(TRUE));
        assert usbtd_is_slot_ref_target_slot(va_get_globals(va_s73), va_get_reg(EAX, va_s73),
          in_target_td_slot);  // line 183 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        va_s69 := va_lemma_empty(va_s73, va_s69);
      }
      else
      {
        ghost var va_b75 := va_get_block(va_get_ifFalse(va_c69));
        assert !(TestBit(usbtd_map_get_flags(va_get_globals(va_s70), va_get_reg(EAX, va_s70)),
          USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 187 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        assert !(usbtd_is_slot_ref_target_slot(va_get_globals(va_s70), va_get_reg(EAX, va_s70),
          in_target_td_slot) && TestBit(usbtd_map_get_flags(va_get_globals(va_s70), va_get_reg(EAX,
          va_s70)), USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 188 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        ghost var va_s78, va_c78, va_b78 := va_lemma_block(va_b75, va_s70, va_s69);
        ghost var va_cond_c78, va_s79:va_state := va_lemma_ifElse(va_get_ifCond(va_c78),
          va_get_ifTrue(va_c78), va_get_ifFalse(va_c78), va_s70, va_s78);
        if (va_cond_c78)
        {
          ghost var va_b80 := va_get_block(va_get_ifTrue(va_c78));
          ghost var va_b81, va_s81 := va_lemma_MOV_ToReg(va_b80, va_s79, va_s78,
            va_op_reg_reg(ESI), va_const_word(FALSE));
          va_s78 := va_lemma_empty(va_s81, va_s78);
        }
        else
        {
          ghost var va_b82 := va_get_block(va_get_ifFalse(va_c78));
          ghost var va_b83, va_s83 := va_lemma_ADD(va_b82, va_s79, va_s78, va_op_word_reg(EAX),
            va_const_word(1));
          ghost var va_b84, va_s84 := va_lemma_MOV_ToReg(va_b83, va_s83, va_s78,
            va_op_reg_reg(ESI), va_const_word(TRUE));
          va_s78 := va_lemma_empty(va_s84, va_s78);
        }
        va_s69 := va_lemma_empty(va_s78, va_s69);
      }
      va_s65 := va_lemma_empty(va_s69, va_s65);
    }
    else
    {
      ghost var va_b85 := va_get_block(va_get_ifFalse(va_c65));
      ghost var va_s86, va_c86, va_b86 := va_lemma_block(va_b85, va_s66, va_s65);
      ghost var va_cond_c86, va_s87:va_state := va_lemma_ifElse(va_get_ifCond(va_c86),
        va_get_ifTrue(va_c86), va_get_ifFalse(va_c86), va_s66, va_s86);
      if (va_cond_c86)
      {
        ghost var va_b88 := va_get_block(va_get_ifTrue(va_c86));
        ghost var va_b89, va_s89 := va_lemma_MOV_ToReg(va_b88, va_s87, va_s86, va_op_reg_reg(ESI),
          va_const_word(FALSE));
        assert !(usbtd_is_slot_ref_target_slot(va_get_globals(va_s89), va_get_reg(EAX, va_s89),
          in_target_td_slot));  // line 205 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        assert !(usbtd_is_slot_ref_target_slot(va_get_globals(va_s89), va_get_reg(EAX, va_s89),
          in_target_td_slot) && TestBit(usbtd_map_get_flags(va_get_globals(va_s89), va_get_reg(EAX,
          va_s89)), USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 206 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        va_s86 := va_lemma_empty(va_s89, va_s86);
      }
      else
      {
        ghost var va_b92 := va_get_block(va_get_ifFalse(va_c86));
        assert !(usbtd_is_slot_ref_target_slot(va_get_globals(va_s87), va_get_reg(EAX, va_s87),
          in_target_td_slot));  // line 211 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        assert !(usbtd_is_slot_ref_target_slot(va_get_globals(va_s87), va_get_reg(EAX, va_s87),
          in_target_td_slot) && TestBit(usbtd_map_get_flags(va_get_globals(va_s87), va_get_reg(EAX,
          va_s87)), USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 212 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        ghost var va_b95, va_s95 := va_lemma_ADD(va_b92, va_s87, va_s86, va_op_word_reg(EAX),
          va_const_word(1));
        ghost var va_b96, va_s96 := va_lemma_MOV_ToReg(va_b95, va_s95, va_s86, va_op_reg_reg(ESI),
          va_const_word(TRUE));
        va_s86 := va_lemma_empty(va_s96, va_s86);
      }
      va_s65 := va_lemma_empty(va_s86, va_s65);
    }
    if (va_get_reg(EBX, va_s65) == FALSE)
    {
      assert !(usbtd_is_slot_ref_target_slot(va_get_globals(va_s65), cur_i, in_target_td_slot) &&
        TestBit(usbtd_map_get_flags(va_get_globals(va_s65), cur_i),
        USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 221 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert forall j:uint32 :: 0 <= j < va_get_reg(EAX, va_s65) && usbtd_map_valid_slot_id(j) ==>
        !(usbtd_is_slot_ref_target_slot(va_get_globals(va_s65), j, in_target_td_slot) &&
        TestBit(usbtd_map_get_flags(va_get_globals(va_s65), j), USBTD_SLOT_FLAG_SlotSecure_Bit)); 
        // line 224 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    }
    Lemma_modify_regs_stateeq(old_this, va_s65);
    va_sW47 := va_lemma_empty(va_s65, va_sW47);
    va_sW46 := va_sW47;
    va_n46 := va_n46 - 1;
  }
  va_s45 := va_lemma_whileFalse(va_get_whileCond(va_c45), va_get_whileBody(va_c45), va_sW46,
    va_s45);
  assert va_get_reg(ECX, va_s45) == TRUE && va_get_reg(EDX, va_s45) == TRUE <==> va_get_reg(EBX,
    va_s45) == TRUE;  // line 233 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
  ghost var t_ret_ref := va_get_reg(ECX, va_s45);
  ghost var t_ret_flag := va_get_reg(EDX, va_s45);
  ghost var t_found_slot := va_get_reg(EBX, va_s45);
  ghost var va_s103, va_c103, va_b103 := va_lemma_block(va_b45, va_s45, va_sM);
  ghost var va_cond_c103, va_s104:va_state := va_lemma_ifElse(va_get_ifCond(va_c103),
    va_get_ifTrue(va_c103), va_get_ifFalse(va_c103), va_s45, va_s103);
  if (va_cond_c103)
  {
    ghost var va_b105 := va_get_block(va_get_ifTrue(va_c103));
    ghost var va_s106, va_c106, va_b106 := va_lemma_block(va_b105, va_s104, va_s103);
    ghost var va_cond_c106, va_s107:va_state := va_lemma_ifElse(va_get_ifCond(va_c106),
      va_get_ifTrue(va_c106), va_get_ifFalse(va_c106), va_s104, va_s106);
    if (va_cond_c106)
    {
      ghost var va_b108 := va_get_block(va_get_ifTrue(va_c106));
      assert va_get_reg(EBX, va_s107) == TRUE;  // line 241 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      ghost var va_b110, va_s110 := va_lemma_Store(va_b108, va_s107, va_s106, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      ghost var va_b111, va_s111 := va_lemma_Store(va_b110, va_s110, va_s106, va_op_word_reg(EBP),
        2 * ARCH_WORD_BYTES, va_op_word_reg(EAX));
      va_s106 := va_lemma_empty(va_s111, va_s106);
    }
    else
    {
      ghost var va_b112 := va_get_block(va_get_ifFalse(va_c106));
      assert t_ret_ref == va_get_reg(ECX, va_s107);  // line 248 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert t_ret_flag == va_get_reg(EDX, va_s107);  // line 249 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert t_found_slot == va_get_reg(EBX, va_s107);  // line 250 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert va_get_reg(EBX, va_s107) == FALSE;  // line 252 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert va_get_reg(EAX, va_s107) == USB_TD_ENTRY_NUM - 1;  // line 253 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      ghost var va_b118, va_s118 := va_lemma_Store(va_b112, va_s107, va_s106, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b119, va_s119 := va_lemma_Store(va_b118, va_s118, va_s106, va_op_word_reg(EBP),
        2 * ARCH_WORD_BYTES, va_const_word(USBTD_SlotID_INVALID));
      va_s106 := va_lemma_empty(va_s119, va_s106);
    }
    va_s103 := va_lemma_empty(va_s106, va_s103);
  }
  else
  {
    ghost var va_b120 := va_get_block(va_get_ifFalse(va_c103));
    assert t_ret_ref == va_get_reg(ECX, va_s104);  // line 261 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    assert t_ret_flag == va_get_reg(EDX, va_s104);  // line 262 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    assert t_found_slot == va_get_reg(EBX, va_s104);  // line 263 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    assert va_get_reg(EBX, va_s104) == FALSE;  // line 265 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    assert va_get_reg(EAX, va_s104) == USB_TD_ENTRY_NUM - 1;  // line 266 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    ghost var va_b126, va_s126 := va_lemma_Store(va_b120, va_s104, va_s103, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b127, va_s127 := va_lemma_Store(va_b126, va_s126, va_s103, va_op_word_reg(EBP), 2
      * ARCH_WORD_BYTES, va_const_word(USBTD_SlotID_INVALID));
    va_s103 := va_lemma_empty(va_s127, va_s103);
  }
  ghost var va_b128, va_s128 := va_lemma_POP_Reg1ToReg6(va_b103, va_s103, va_sM);
  ghost var va_b129, va_s129 := va_lemma_POP_OneReg(va_b128, va_s128, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s129, va_sM);
}
//--
//-- _wimpdrv_find_referencing_secure_usbtd

function method{:opaque} va_code__wimpdrv_find_referencing_secure_usbtd():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_usbtd_check_wimpdrv_slotid(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbtd_get_flags(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_TestBit(va_op_word_reg(EDI),
    USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(FALSE)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)), va_CNil()))),
    va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)),
    va_CNil()))), va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_usbtd_check_wimpdrv_slotid(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbtd_get_flags(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_TestBit(va_op_word_reg(EDI),
    USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(FALSE)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(USB_TD_ENTRY_NUM - 1)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)), va_CNil())))),
    va_CNil()))), va_CNil())), va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX),
    va_const_cmp(USB_TD_ENTRY_NUM - 1)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI),
    va_const_word(FALSE)), va_CNil())), va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX),
    va_const_word(1)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)),
    va_CNil())))), va_CNil()))), va_CNil()))))))))))))))),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES, va_op_word_reg(EAX)),
    va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(USBTD_SlotID_INVALID)), va_CNil())))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(USBTD_SlotID_INVALID)), va_CNil())))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))))))))))
}

lemma{:timeLimitMultiplier 200} va_lemma__wimpdrv_find_referencing_secure_usbtd(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__wimpdrv_find_referencing_secure_usbtd(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 11 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var target_wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); wimpdrv_valid_slot_id(target_wimpdrv_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var target_wimpdrv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    src_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    (((ret == TRUE ==> usbtd_map_valid_slot_id(src_slot)) && (ret == TRUE ==>
    TestBit(usbtd_map_get_flags(va_get_globals(va_s0), src_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)))
    && (ret == TRUE ==> usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s0), src_slot) ==
    target_wimpdrv_slot)) && (ret != TRUE ==>
    usbtds_verifiedtds_do_not_associate_wimpdrv(va_get_globals(va_s0), target_wimpdrv_slot))
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
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code__wimpdrv_find_referencing_secure_usbtd();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_p_ffi_usbtd_is_ref_target_usbtd_retval();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b11, va_s11 := va_lemma_PUSH_Reg1ToReg6(va_b4, va_s4, va_sM);
  ghost var begin_state := va_s11;
  ghost var orig_ebp := va_get_reg(EBP, va_s11);
  ghost var va_b14, va_s14 := va_lemma_MOV_ToReg(va_b11, va_s11, va_sM, va_op_reg_reg(EAX),
    va_const_word(0));
  ghost var va_b15, va_s15 := va_lemma_MOV_ToReg(va_b14, va_s14, va_sM, va_op_reg_reg(ESI),
    va_const_word(TRUE));
  ghost var va_b16, va_s16 := va_lemma_MOV_ToReg(va_b15, va_s15, va_sM, va_op_reg_reg(ECX),
    va_const_word(TRUE));
  ghost var va_b17, va_s17 := va_lemma_MOV_ToReg(va_b16, va_s16, va_sM, va_op_reg_reg(EDX),
    va_const_word(TRUE));
  ghost var va_b18, va_s18 := va_lemma_Load(va_b17, va_s17, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var in_target_slot := va_get_reg(EDI, va_s18);
  ghost var va_b20, va_s20 := va_lemma_PUSH(va_b18, va_s18, va_sM, va_op_word_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s20, va_sM, va_op_word_reg(EAX));
  ghost var va_b22, va_s22 := va_lemma_usbtd_check_wimpdrv_slotid(va_b21, va_s21, va_sM);
  ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0);
  ghost var va_b24, va_s24 := va_lemma_POP_VOID(va_b23, va_s23, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_b25, va_s25 := va_lemma_PUSH(va_b24, va_s24, va_sM, va_op_word_reg(EAX));
  ghost var va_b26, va_s26 := va_lemma_usbtd_get_flags(va_b25, va_s25, va_sM);
  ghost var va_b27, va_s27 := va_lemma_Load(va_b26, va_s26, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0);
  ghost var va_b28, va_s28 := va_lemma_POP_VOID(va_b27, va_s27, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b29, va_s29 := va_lemma_TestBit(va_b28, va_s28, va_sM, va_op_word_reg(EDI),
    USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX));
  ghost var va_b30, va_s30 := va_lemma_MOV_ToReg(va_b29, va_s29, va_sM, va_op_reg_reg(EBX),
    va_const_word(FALSE));
  ghost var va_s31, va_c31, va_b31 := va_lemma_block(va_b30, va_s30, va_sM);
  ghost var va_cond_c31, va_s32:va_state := va_lemma_ifElse(va_get_ifCond(va_c31),
    va_get_ifTrue(va_c31), va_get_ifFalse(va_c31), va_s30, va_s31);
  if (va_cond_c31)
  {
    ghost var va_b33 := va_get_block(va_get_ifTrue(va_c31));
    ghost var va_s34, va_c34, va_b34 := va_lemma_block(va_b33, va_s32, va_s31);
    ghost var va_cond_c34, va_s35:va_state := va_lemma_ifElse(va_get_ifCond(va_c34),
      va_get_ifTrue(va_c34), va_get_ifFalse(va_c34), va_s32, va_s34);
    if (va_cond_c34)
    {
      ghost var va_b36 := va_get_block(va_get_ifTrue(va_c34));
      ghost var va_b37, va_s37 := va_lemma_MOV_ToReg(va_b36, va_s35, va_s34, va_op_reg_reg(ESI),
        va_const_word(FALSE));
      ghost var va_b38, va_s38 := va_lemma_MOV_ToReg(va_b37, va_s37, va_s34, va_op_reg_reg(EBX),
        va_const_word(TRUE));
      va_s34 := va_lemma_empty(va_s38, va_s34);
    }
    else
    {
      ghost var va_b39 := va_get_block(va_get_ifFalse(va_c34));
      ghost var va_b40, va_s40 := va_lemma_MOV_ToReg(va_b39, va_s35, va_s34, va_op_reg_reg(ESI),
        va_const_word(TRUE));
      va_s34 := va_lemma_empty(va_s40, va_s34);
    }
    va_s31 := va_lemma_empty(va_s34, va_s31);
  }
  else
  {
    ghost var va_b41 := va_get_block(va_get_ifFalse(va_c31));
    ghost var va_b42, va_s42 := va_lemma_MOV_ToReg(va_b41, va_s32, va_s31, va_op_reg_reg(ESI),
      va_const_word(TRUE));
    va_s31 := va_lemma_empty(va_s42, va_s31);
  }
  ghost var va_s43, va_c43, va_b43 := va_lemma_block(va_b31, va_s31, va_sM);
  ghost var va_n44:int, va_sW44:va_state := va_lemma_while(va_get_whileCond(va_c43),
    va_get_whileBody(va_c43), va_s31, va_s43);
  while (va_n44 > 0)
    invariant va_whileInv(va_get_whileCond(va_c43), va_get_whileBody(va_c43), va_n44, va_sW44,
      va_s43)
    invariant va_get_ok(va_sW44)
    invariant 0 <= va_get_reg(EAX, va_sW44) <= USB_TD_ENTRY_NUM
    invariant va_get_reg(ESI, va_sW44) == TRUE ==> 0 <= va_get_reg(EAX, va_sW44) < USB_TD_ENTRY_NUM
    invariant va_get_reg(EBX, va_sW44) == TRUE || va_get_reg(EBX, va_sW44) == FALSE
    invariant va_get_reg(ESI, va_sW44) == TRUE ==> va_get_reg(EBX, va_sW44) == FALSE
    invariant va_get_reg(EBX, va_sW44) == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX,
      va_sW44) && usbtd_map_valid_slot_id(j) ==>
      !(usbtd_map_get_wimpdrv_slotid(va_get_globals(va_sW44), j) == in_target_slot &&
      TestBit(usbtd_map_get_flags(va_get_globals(va_sW44), j), USBTD_SLOT_FLAG_SlotSecure_Bit)))
    invariant va_get_reg(ESI, va_sW44) != TRUE && va_get_reg(EBX, va_sW44) == FALSE ==> (forall
      j:uint32 :: usbtd_map_valid_slot_id(j) ==>
      !(usbtd_map_get_wimpdrv_slotid(va_get_globals(va_sW44), j) == in_target_slot &&
      TestBit(usbtd_map_get_flags(va_get_globals(va_sW44), j), USBTD_SLOT_FLAG_SlotSecure_Bit)))
    invariant va_get_reg(ESI, va_sW44) != TRUE ==> (va_get_reg(ECX, va_sW44) == TRUE &&
      va_get_reg(EDX, va_sW44) == TRUE <==> va_get_reg(EBX, va_sW44) == TRUE)
    invariant va_get_reg(ESI, va_sW44) != TRUE ==> (va_get_reg(ECX, va_sW44) == TRUE &&
      va_get_reg(EDX, va_sW44) == TRUE) || va_get_reg(EAX, va_sW44) == USB_TD_ENTRY_NUM - 1
    invariant va_get_reg(ESI, va_sW44) != TRUE && (va_get_reg(ECX, va_sW44) == TRUE &&
      va_get_reg(EDX, va_sW44) == TRUE) ==> (usbtd_map_valid_slot_id(va_get_reg(EAX, va_sW44)) &&
      TestBit(usbtd_map_get_flags(va_get_globals(va_sW44), va_get_reg(EAX, va_sW44)),
      USBTD_SLOT_FLAG_SlotSecure_Bit)) && usbtd_map_get_wimpdrv_slotid(va_get_globals(va_sW44),
      va_get_reg(EAX, va_sW44)) == in_target_slot
    invariant va_get_reg(ESP, va_sW44) == va_get_reg(ESP, va_old_s) - 7 * ARCH_WORD_BYTES
    invariant stack_under_sp_is_unchanged(begin_state.wk_mstate.m, va_sW44.wk_mstate.m,
      va_get_reg(ESP, va_sW44))
    invariant va_get_globals(va_sW44) == va_get_globals(va_old_s)
    invariant va_get_reg(EBP, va_sW44) == orig_ebp
    invariant state_equal_except_mstate(va_old_s, va_sW44)
    invariant va_state_eq(va_sW44, va_update_reg(EDX, va_sW44, va_update_reg(ECX, va_sW44,
      va_update_reg(EBX, va_sW44, va_update_reg(EAX, va_sW44, va_update_reg(EDI, va_sW44,
      va_update_reg(ESI, va_sW44, va_update_mem(va_sW44, va_update_reg(ESP, va_sW44,
      va_update_reg(EBP, va_sW44, va_update_ok(va_sW44, va_s0)))))))))))
    decreases USB_TD_ENTRY_NUM - va_get_reg(EAX, va_sW44), va_get_reg(ESI, va_sW44)
  {
    ghost var va_s44:va_state, va_sW45:va_state := va_lemma_whileTrue(va_get_whileCond(va_c43),
      va_get_whileBody(va_c43), va_n44, va_sW44, va_s43);
    ghost var va_b46 := va_get_block(va_get_whileBody(va_c43));
    ghost var old_this := va_s44;
    ghost var va_b48, va_s48 := va_lemma_Load(va_b46, va_s44, va_sW45, va_op_word_reg(EDI),
      va_op_word_reg(EBP), ARCH_WORD_BYTES);
    ghost var va_b49, va_s49 := va_lemma_PUSH(va_b48, va_s48, va_sW45, va_op_word_reg(EDI));
    ghost var va_b50, va_s50 := va_lemma_PUSH(va_b49, va_s49, va_sW45, va_op_word_reg(EAX));
    ghost var va_b51, va_s51 := va_lemma_usbtd_check_wimpdrv_slotid(va_b50, va_s50, va_sW45);
    ghost var va_b52, va_s52 := va_lemma_Load(va_b51, va_s51, va_sW45, va_op_word_reg(ECX),
      va_op_word_reg(ESP), 0);
    ghost var va_b53, va_s53 := va_lemma_POP_VOID(va_b52, va_s52, va_sW45, 2 * ARCH_WORD_BYTES);
    ghost var va_b54, va_s54 := va_lemma_PUSH(va_b53, va_s53, va_sW45, va_op_word_reg(EAX));
    ghost var va_b55, va_s55 := va_lemma_usbtd_get_flags(va_b54, va_s54, va_sW45);
    ghost var va_b56, va_s56 := va_lemma_Load(va_b55, va_s55, va_sW45, va_op_word_reg(EDI),
      va_op_word_reg(ESP), 0);
    ghost var va_b57, va_s57 := va_lemma_POP_VOID(va_b56, va_s56, va_sW45, 1 * ARCH_WORD_BYTES);
    ghost var va_b58, va_s58 := va_lemma_TestBit(va_b57, va_s57, va_sW45, va_op_word_reg(EDI),
      USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX));
    ghost var va_b59, va_s59 := va_lemma_MOV_ToReg(va_b58, va_s58, va_sW45, va_op_reg_reg(EBX),
      va_const_word(FALSE));
    ghost var cur_i := va_get_reg(EAX, va_s59);
    ghost var va_s61, va_c61, va_b61 := va_lemma_block(va_b59, va_s59, va_sW45);
    ghost var va_cond_c61, va_s62:va_state := va_lemma_ifElse(va_get_ifCond(va_c61),
      va_get_ifTrue(va_c61), va_get_ifFalse(va_c61), va_s59, va_s61);
    if (va_cond_c61)
    {
      ghost var va_b63 := va_get_block(va_get_ifTrue(va_c61));
      assert usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s62), va_get_reg(EAX, va_s62)) ==
        in_target_slot;  // line 440 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      ghost var va_s65, va_c65, va_b65 := va_lemma_block(va_b63, va_s62, va_s61);
      ghost var va_cond_c65, va_s66:va_state := va_lemma_ifElse(va_get_ifCond(va_c65),
        va_get_ifTrue(va_c65), va_get_ifFalse(va_c65), va_s62, va_s65);
      if (va_cond_c65)
      {
        ghost var va_b67 := va_get_block(va_get_ifTrue(va_c65));
        ghost var va_b68, va_s68 := va_lemma_MOV_ToReg(va_b67, va_s66, va_s65, va_op_reg_reg(ESI),
          va_const_word(FALSE));
        ghost var va_b69, va_s69 := va_lemma_MOV_ToReg(va_b68, va_s68, va_s65, va_op_reg_reg(EBX),
          va_const_word(TRUE));
        assert usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s69), va_get_reg(EAX, va_s69)) ==
          in_target_slot;  // line 445 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        va_s65 := va_lemma_empty(va_s69, va_s65);
      }
      else
      {
        ghost var va_b71 := va_get_block(va_get_ifFalse(va_c65));
        assert !(TestBit(usbtd_map_get_flags(va_get_globals(va_s66), va_get_reg(EAX, va_s66)),
          USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 449 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        assert !(usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s66), va_get_reg(EAX, va_s66)) ==
          in_target_slot && TestBit(usbtd_map_get_flags(va_get_globals(va_s66), va_get_reg(EAX,
          va_s66)), USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 450 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        ghost var va_s74, va_c74, va_b74 := va_lemma_block(va_b71, va_s66, va_s65);
        ghost var va_cond_c74, va_s75:va_state := va_lemma_ifElse(va_get_ifCond(va_c74),
          va_get_ifTrue(va_c74), va_get_ifFalse(va_c74), va_s66, va_s74);
        if (va_cond_c74)
        {
          ghost var va_b76 := va_get_block(va_get_ifTrue(va_c74));
          ghost var va_b77, va_s77 := va_lemma_MOV_ToReg(va_b76, va_s75, va_s74,
            va_op_reg_reg(ESI), va_const_word(FALSE));
          va_s74 := va_lemma_empty(va_s77, va_s74);
        }
        else
        {
          ghost var va_b78 := va_get_block(va_get_ifFalse(va_c74));
          ghost var va_b79, va_s79 := va_lemma_ADD(va_b78, va_s75, va_s74, va_op_word_reg(EAX),
            va_const_word(1));
          ghost var va_b80, va_s80 := va_lemma_MOV_ToReg(va_b79, va_s79, va_s74,
            va_op_reg_reg(ESI), va_const_word(TRUE));
          va_s74 := va_lemma_empty(va_s80, va_s74);
        }
        va_s65 := va_lemma_empty(va_s74, va_s65);
      }
      va_s61 := va_lemma_empty(va_s65, va_s61);
    }
    else
    {
      ghost var va_b81 := va_get_block(va_get_ifFalse(va_c61));
      ghost var va_s82, va_c82, va_b82 := va_lemma_block(va_b81, va_s62, va_s61);
      ghost var va_cond_c82, va_s83:va_state := va_lemma_ifElse(va_get_ifCond(va_c82),
        va_get_ifTrue(va_c82), va_get_ifFalse(va_c82), va_s62, va_s82);
      if (va_cond_c82)
      {
        ghost var va_b84 := va_get_block(va_get_ifTrue(va_c82));
        ghost var va_b85, va_s85 := va_lemma_MOV_ToReg(va_b84, va_s83, va_s82, va_op_reg_reg(ESI),
          va_const_word(FALSE));
        assert !(usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s85), va_get_reg(EAX, va_s85)) ==
          in_target_slot);  // line 467 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        assert !(usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s85), va_get_reg(EAX, va_s85)) ==
          in_target_slot && TestBit(usbtd_map_get_flags(va_get_globals(va_s85), va_get_reg(EAX,
          va_s85)), USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 468 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        va_s82 := va_lemma_empty(va_s85, va_s82);
      }
      else
      {
        ghost var va_b88 := va_get_block(va_get_ifFalse(va_c82));
        assert !(usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s83), va_get_reg(EAX, va_s83)) ==
          in_target_slot);  // line 473 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        assert !(usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s83), va_get_reg(EAX, va_s83)) ==
          in_target_slot && TestBit(usbtd_map_get_flags(va_get_globals(va_s83), va_get_reg(EAX,
          va_s83)), USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 474 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        ghost var va_b91, va_s91 := va_lemma_ADD(va_b88, va_s83, va_s82, va_op_word_reg(EAX),
          va_const_word(1));
        ghost var va_b92, va_s92 := va_lemma_MOV_ToReg(va_b91, va_s91, va_s82, va_op_reg_reg(ESI),
          va_const_word(TRUE));
        va_s82 := va_lemma_empty(va_s92, va_s82);
      }
      va_s61 := va_lemma_empty(va_s82, va_s61);
    }
    if (va_get_reg(EBX, va_s61) == FALSE)
    {
      assert !(usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s61), cur_i) == in_target_slot &&
        TestBit(usbtd_map_get_flags(va_get_globals(va_s61), cur_i),
        USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 483 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert forall j:uint32 :: 0 <= j < va_get_reg(EAX, va_s61) && usbtd_map_valid_slot_id(j) ==>
        !(usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s61), j) == in_target_slot &&
        TestBit(usbtd_map_get_flags(va_get_globals(va_s61), j), USBTD_SLOT_FLAG_SlotSecure_Bit)); 
        // line 486 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    }
    Lemma_modify_regs_stateeq(old_this, va_s61);
    va_sW45 := va_lemma_empty(va_s61, va_sW45);
    va_sW44 := va_sW45;
    va_n44 := va_n44 - 1;
  }
  va_s43 := va_lemma_whileFalse(va_get_whileCond(va_c43), va_get_whileBody(va_c43), va_sW44,
    va_s43);
  assert va_get_reg(ECX, va_s43) == TRUE && va_get_reg(EDX, va_s43) == TRUE <==> va_get_reg(EBX,
    va_s43) == TRUE;  // line 495 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
  ghost var t_ret_ref := va_get_reg(ECX, va_s43);
  ghost var t_ret_flag := va_get_reg(EDX, va_s43);
  ghost var t_found_slot := va_get_reg(EBX, va_s43);
  ghost var va_s99, va_c99, va_b99 := va_lemma_block(va_b43, va_s43, va_sM);
  ghost var va_cond_c99, va_s100:va_state := va_lemma_ifElse(va_get_ifCond(va_c99),
    va_get_ifTrue(va_c99), va_get_ifFalse(va_c99), va_s43, va_s99);
  if (va_cond_c99)
  {
    ghost var va_b101 := va_get_block(va_get_ifTrue(va_c99));
    ghost var va_s102, va_c102, va_b102 := va_lemma_block(va_b101, va_s100, va_s99);
    ghost var va_cond_c102, va_s103:va_state := va_lemma_ifElse(va_get_ifCond(va_c102),
      va_get_ifTrue(va_c102), va_get_ifFalse(va_c102), va_s100, va_s102);
    if (va_cond_c102)
    {
      ghost var va_b104 := va_get_block(va_get_ifTrue(va_c102));
      assert va_get_reg(EBX, va_s103) == TRUE;  // line 503 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      ghost var va_b106, va_s106 := va_lemma_Store(va_b104, va_s103, va_s102, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      ghost var va_b107, va_s107 := va_lemma_Store(va_b106, va_s106, va_s102, va_op_word_reg(EBP),
        2 * ARCH_WORD_BYTES, va_op_word_reg(EAX));
      va_s102 := va_lemma_empty(va_s107, va_s102);
    }
    else
    {
      ghost var va_b108 := va_get_block(va_get_ifFalse(va_c102));
      assert t_ret_ref == va_get_reg(ECX, va_s103);  // line 510 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert t_ret_flag == va_get_reg(EDX, va_s103);  // line 511 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert t_found_slot == va_get_reg(EBX, va_s103);  // line 512 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert va_get_reg(EBX, va_s103) == FALSE;  // line 514 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert va_get_reg(EAX, va_s103) == USB_TD_ENTRY_NUM - 1;  // line 515 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      ghost var va_b114, va_s114 := va_lemma_Store(va_b108, va_s103, va_s102, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b115, va_s115 := va_lemma_Store(va_b114, va_s114, va_s102, va_op_word_reg(EBP),
        2 * ARCH_WORD_BYTES, va_const_word(USBTD_SlotID_INVALID));
      va_s102 := va_lemma_empty(va_s115, va_s102);
    }
    va_s99 := va_lemma_empty(va_s102, va_s99);
  }
  else
  {
    ghost var va_b116 := va_get_block(va_get_ifFalse(va_c99));
    assert t_ret_ref == va_get_reg(ECX, va_s100);  // line 523 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    assert t_ret_flag == va_get_reg(EDX, va_s100);  // line 524 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    assert t_found_slot == va_get_reg(EBX, va_s100);  // line 525 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    assert va_get_reg(EBX, va_s100) == FALSE;  // line 527 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    assert va_get_reg(EAX, va_s100) == USB_TD_ENTRY_NUM - 1;  // line 528 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    ghost var va_b122, va_s122 := va_lemma_Store(va_b116, va_s100, va_s99, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b123, va_s123 := va_lemma_Store(va_b122, va_s122, va_s99, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(USBTD_SlotID_INVALID));
    va_s99 := va_lemma_empty(va_s123, va_s99);
  }
  reveal_usbtds_verifiedtds_do_not_associate_wimpdrv();
  ghost var va_b125, va_s125 := va_lemma_POP_Reg1ToReg6(va_b99, va_s99, va_sM);
  ghost var va_b126, va_s126 := va_lemma_POP_OneReg(va_b125, va_s125, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s126, va_sM);
}
//--
//-- _usbpdev_find_referencing_secure_usbtd

function method{:opaque} va_code__usbpdev_find_referencing_secure_usbtd():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(0)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_const_word(TRUE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(TRUE)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_usbtd_check_usbpdev_slotid(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbtd_get_flags(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_TestBit(va_op_word_reg(EDI),
    USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(FALSE)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)), va_CNil()))),
    va_CNil())), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)),
    va_CNil()))), va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_usbtd_check_usbpdev_slotid(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbtd_get_flags(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_TestBit(va_op_word_reg(EDI),
    USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(FALSE)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(FALSE)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(TRUE)), va_CNil()))),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(USB_TD_ENTRY_NUM - 1)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX), va_const_word(1)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)), va_CNil())))),
    va_CNil()))), va_CNil())), va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX),
    va_const_cmp(USB_TD_ENTRY_NUM - 1)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI),
    va_const_word(FALSE)), va_CNil())), va_Block(va_CCons(va_code_ADD(va_op_word_reg(EAX),
    va_const_word(1)), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ESI), va_const_word(TRUE)),
    va_CNil())))), va_CNil()))), va_CNil()))))))))))))))),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES, va_op_word_reg(EAX)),
    va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(USBTD_SlotID_INVALID)), va_CNil())))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(USBTD_SlotID_INVALID)), va_CNil())))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))))))))))
}

lemma{:timeLimitMultiplier 100} va_lemma__usbpdev_find_referencing_secure_usbtd(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbpdev_find_referencing_secure_usbtd(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 11 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var target_usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); usbpdev_valid_slot_id(target_usbpdev_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var target_usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0)); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var
    src_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    (((ret == TRUE ==> usbtd_map_valid_slot_id(src_slot)) && (ret == TRUE ==>
    TestBit(usbtd_map_get_flags(va_get_globals(va_s0), src_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)))
    && (ret == TRUE ==> usbtd_map_get_usbpdev_slotid(va_get_globals(va_s0), src_slot) ==
    target_usbpdev_slot)) && (ret != TRUE ==>
    usbtds_verifiedtds_do_not_associate_usb_pdev(va_get_globals(va_s0), target_usbpdev_slot))
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
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code__usbpdev_find_referencing_secure_usbtd();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_p_ffi_usbtd_is_ref_target_usbtd_retval();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b11, va_s11 := va_lemma_PUSH_Reg1ToReg6(va_b4, va_s4, va_sM);
  ghost var begin_state := va_s11;
  ghost var orig_ebp := va_get_reg(EBP, va_s11);
  ghost var va_b14, va_s14 := va_lemma_MOV_ToReg(va_b11, va_s11, va_sM, va_op_reg_reg(EAX),
    va_const_word(0));
  ghost var va_b15, va_s15 := va_lemma_MOV_ToReg(va_b14, va_s14, va_sM, va_op_reg_reg(ESI),
    va_const_word(TRUE));
  ghost var va_b16, va_s16 := va_lemma_MOV_ToReg(va_b15, va_s15, va_sM, va_op_reg_reg(ECX),
    va_const_word(TRUE));
  ghost var va_b17, va_s17 := va_lemma_MOV_ToReg(va_b16, va_s16, va_sM, va_op_reg_reg(EDX),
    va_const_word(TRUE));
  ghost var va_b18, va_s18 := va_lemma_Load(va_b17, va_s17, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var in_target_slot := va_get_reg(EDI, va_s18);
  ghost var va_b20, va_s20 := va_lemma_PUSH(va_b18, va_s18, va_sM, va_op_word_reg(EDI));
  ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s20, va_sM, va_op_word_reg(EAX));
  ghost var va_b22, va_s22 := va_lemma_usbtd_check_usbpdev_slotid(va_b21, va_s21, va_sM);
  ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0);
  ghost var va_b24, va_s24 := va_lemma_POP_VOID(va_b23, va_s23, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_b25, va_s25 := va_lemma_PUSH(va_b24, va_s24, va_sM, va_op_word_reg(EAX));
  ghost var va_b26, va_s26 := va_lemma_usbtd_get_flags(va_b25, va_s25, va_sM);
  ghost var va_b27, va_s27 := va_lemma_Load(va_b26, va_s26, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0);
  ghost var va_b28, va_s28 := va_lemma_POP_VOID(va_b27, va_s27, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b29, va_s29 := va_lemma_TestBit(va_b28, va_s28, va_sM, va_op_word_reg(EDI),
    USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX));
  ghost var va_b30, va_s30 := va_lemma_MOV_ToReg(va_b29, va_s29, va_sM, va_op_reg_reg(EBX),
    va_const_word(FALSE));
  ghost var va_s31, va_c31, va_b31 := va_lemma_block(va_b30, va_s30, va_sM);
  ghost var va_cond_c31, va_s32:va_state := va_lemma_ifElse(va_get_ifCond(va_c31),
    va_get_ifTrue(va_c31), va_get_ifFalse(va_c31), va_s30, va_s31);
  if (va_cond_c31)
  {
    ghost var va_b33 := va_get_block(va_get_ifTrue(va_c31));
    ghost var va_s34, va_c34, va_b34 := va_lemma_block(va_b33, va_s32, va_s31);
    ghost var va_cond_c34, va_s35:va_state := va_lemma_ifElse(va_get_ifCond(va_c34),
      va_get_ifTrue(va_c34), va_get_ifFalse(va_c34), va_s32, va_s34);
    if (va_cond_c34)
    {
      ghost var va_b36 := va_get_block(va_get_ifTrue(va_c34));
      ghost var va_b37, va_s37 := va_lemma_MOV_ToReg(va_b36, va_s35, va_s34, va_op_reg_reg(ESI),
        va_const_word(FALSE));
      ghost var va_b38, va_s38 := va_lemma_MOV_ToReg(va_b37, va_s37, va_s34, va_op_reg_reg(EBX),
        va_const_word(TRUE));
      va_s34 := va_lemma_empty(va_s38, va_s34);
    }
    else
    {
      ghost var va_b39 := va_get_block(va_get_ifFalse(va_c34));
      ghost var va_b40, va_s40 := va_lemma_MOV_ToReg(va_b39, va_s35, va_s34, va_op_reg_reg(ESI),
        va_const_word(TRUE));
      va_s34 := va_lemma_empty(va_s40, va_s34);
    }
    va_s31 := va_lemma_empty(va_s34, va_s31);
  }
  else
  {
    ghost var va_b41 := va_get_block(va_get_ifFalse(va_c31));
    ghost var va_b42, va_s42 := va_lemma_MOV_ToReg(va_b41, va_s32, va_s31, va_op_reg_reg(ESI),
      va_const_word(TRUE));
    va_s31 := va_lemma_empty(va_s42, va_s31);
  }
  ghost var va_s43, va_c43, va_b43 := va_lemma_block(va_b31, va_s31, va_sM);
  ghost var va_n44:int, va_sW44:va_state := va_lemma_while(va_get_whileCond(va_c43),
    va_get_whileBody(va_c43), va_s31, va_s43);
  while (va_n44 > 0)
    invariant va_whileInv(va_get_whileCond(va_c43), va_get_whileBody(va_c43), va_n44, va_sW44,
      va_s43)
    invariant va_get_ok(va_sW44)
    invariant 0 <= va_get_reg(EAX, va_sW44) <= USB_TD_ENTRY_NUM
    invariant va_get_reg(ESI, va_sW44) == TRUE ==> 0 <= va_get_reg(EAX, va_sW44) < USB_TD_ENTRY_NUM
    invariant va_get_reg(EBX, va_sW44) == TRUE || va_get_reg(EBX, va_sW44) == FALSE
    invariant va_get_reg(ESI, va_sW44) == TRUE ==> va_get_reg(EBX, va_sW44) == FALSE
    invariant va_get_reg(EBX, va_sW44) == FALSE ==> (forall j:uint32 :: 0 <= j < va_get_reg(EAX,
      va_sW44) && usbtd_map_valid_slot_id(j) ==>
      !(usbtd_map_get_usbpdev_slotid(va_get_globals(va_sW44), j) == in_target_slot &&
      TestBit(usbtd_map_get_flags(va_get_globals(va_sW44), j), USBTD_SLOT_FLAG_SlotSecure_Bit)))
    invariant va_get_reg(ESI, va_sW44) != TRUE && va_get_reg(EBX, va_sW44) == FALSE ==> (forall
      j:uint32 :: usbtd_map_valid_slot_id(j) ==>
      !(usbtd_map_get_usbpdev_slotid(va_get_globals(va_sW44), j) == in_target_slot &&
      TestBit(usbtd_map_get_flags(va_get_globals(va_sW44), j), USBTD_SLOT_FLAG_SlotSecure_Bit)))
    invariant va_get_reg(ESI, va_sW44) != TRUE ==> (va_get_reg(ECX, va_sW44) == TRUE &&
      va_get_reg(EDX, va_sW44) == TRUE <==> va_get_reg(EBX, va_sW44) == TRUE)
    invariant va_get_reg(ESI, va_sW44) != TRUE ==> (va_get_reg(ECX, va_sW44) == TRUE &&
      va_get_reg(EDX, va_sW44) == TRUE) || va_get_reg(EAX, va_sW44) == USB_TD_ENTRY_NUM - 1
    invariant va_get_reg(ESI, va_sW44) != TRUE && (va_get_reg(ECX, va_sW44) == TRUE &&
      va_get_reg(EDX, va_sW44) == TRUE) ==> (usbtd_map_valid_slot_id(va_get_reg(EAX, va_sW44)) &&
      TestBit(usbtd_map_get_flags(va_get_globals(va_sW44), va_get_reg(EAX, va_sW44)),
      USBTD_SLOT_FLAG_SlotSecure_Bit)) && usbtd_map_get_usbpdev_slotid(va_get_globals(va_sW44),
      va_get_reg(EAX, va_sW44)) == in_target_slot
    invariant va_get_reg(ESP, va_sW44) == va_get_reg(ESP, va_old_s) - 7 * ARCH_WORD_BYTES
    invariant stack_under_sp_is_unchanged(begin_state.wk_mstate.m, va_sW44.wk_mstate.m,
      va_get_reg(ESP, va_sW44))
    invariant va_get_globals(va_sW44) == va_get_globals(va_old_s)
    invariant va_get_reg(EBP, va_sW44) == orig_ebp
    invariant state_equal_except_mstate(va_old_s, va_sW44)
    invariant va_state_eq(va_sW44, va_update_reg(EDX, va_sW44, va_update_reg(ECX, va_sW44,
      va_update_reg(EBX, va_sW44, va_update_reg(EAX, va_sW44, va_update_reg(EDI, va_sW44,
      va_update_reg(ESI, va_sW44, va_update_mem(va_sW44, va_update_reg(ESP, va_sW44,
      va_update_reg(EBP, va_sW44, va_update_ok(va_sW44, va_s0)))))))))))
    decreases USB_TD_ENTRY_NUM - va_get_reg(EAX, va_sW44), va_get_reg(ESI, va_sW44)
  {
    ghost var va_s44:va_state, va_sW45:va_state := va_lemma_whileTrue(va_get_whileCond(va_c43),
      va_get_whileBody(va_c43), va_n44, va_sW44, va_s43);
    ghost var va_b46 := va_get_block(va_get_whileBody(va_c43));
    ghost var old_this := va_s44;
    ghost var va_b48, va_s48 := va_lemma_Load(va_b46, va_s44, va_sW45, va_op_word_reg(EDI),
      va_op_word_reg(EBP), ARCH_WORD_BYTES);
    ghost var va_b49, va_s49 := va_lemma_PUSH(va_b48, va_s48, va_sW45, va_op_word_reg(EDI));
    ghost var va_b50, va_s50 := va_lemma_PUSH(va_b49, va_s49, va_sW45, va_op_word_reg(EAX));
    ghost var va_b51, va_s51 := va_lemma_usbtd_check_usbpdev_slotid(va_b50, va_s50, va_sW45);
    ghost var va_b52, va_s52 := va_lemma_Load(va_b51, va_s51, va_sW45, va_op_word_reg(ECX),
      va_op_word_reg(ESP), 0);
    ghost var va_b53, va_s53 := va_lemma_POP_VOID(va_b52, va_s52, va_sW45, 2 * ARCH_WORD_BYTES);
    ghost var va_b54, va_s54 := va_lemma_PUSH(va_b53, va_s53, va_sW45, va_op_word_reg(EAX));
    ghost var va_b55, va_s55 := va_lemma_usbtd_get_flags(va_b54, va_s54, va_sW45);
    ghost var va_b56, va_s56 := va_lemma_Load(va_b55, va_s55, va_sW45, va_op_word_reg(EDI),
      va_op_word_reg(ESP), 0);
    ghost var va_b57, va_s57 := va_lemma_POP_VOID(va_b56, va_s56, va_sW45, 1 * ARCH_WORD_BYTES);
    ghost var va_b58, va_s58 := va_lemma_TestBit(va_b57, va_s57, va_sW45, va_op_word_reg(EDI),
      USBTD_SLOT_FLAG_SlotSecure_Bit, va_op_word_reg(EDX));
    ghost var va_b59, va_s59 := va_lemma_MOV_ToReg(va_b58, va_s58, va_sW45, va_op_reg_reg(EBX),
      va_const_word(FALSE));
    ghost var cur_i := va_get_reg(EAX, va_s59);
    ghost var va_s61, va_c61, va_b61 := va_lemma_block(va_b59, va_s59, va_sW45);
    ghost var va_cond_c61, va_s62:va_state := va_lemma_ifElse(va_get_ifCond(va_c61),
      va_get_ifTrue(va_c61), va_get_ifFalse(va_c61), va_s59, va_s61);
    if (va_cond_c61)
    {
      ghost var va_b63 := va_get_block(va_get_ifTrue(va_c61));
      assert usbtd_map_get_usbpdev_slotid(va_get_globals(va_s62), va_get_reg(EAX, va_s62)) ==
        in_target_slot;  // line 703 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      ghost var va_s65, va_c65, va_b65 := va_lemma_block(va_b63, va_s62, va_s61);
      ghost var va_cond_c65, va_s66:va_state := va_lemma_ifElse(va_get_ifCond(va_c65),
        va_get_ifTrue(va_c65), va_get_ifFalse(va_c65), va_s62, va_s65);
      if (va_cond_c65)
      {
        ghost var va_b67 := va_get_block(va_get_ifTrue(va_c65));
        ghost var va_b68, va_s68 := va_lemma_MOV_ToReg(va_b67, va_s66, va_s65, va_op_reg_reg(ESI),
          va_const_word(FALSE));
        ghost var va_b69, va_s69 := va_lemma_MOV_ToReg(va_b68, va_s68, va_s65, va_op_reg_reg(EBX),
          va_const_word(TRUE));
        assert usbtd_map_get_usbpdev_slotid(va_get_globals(va_s69), va_get_reg(EAX, va_s69)) ==
          in_target_slot;  // line 708 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        va_s65 := va_lemma_empty(va_s69, va_s65);
      }
      else
      {
        ghost var va_b71 := va_get_block(va_get_ifFalse(va_c65));
        assert !(TestBit(usbtd_map_get_flags(va_get_globals(va_s66), va_get_reg(EAX, va_s66)),
          USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 712 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        assert !(usbtd_map_get_usbpdev_slotid(va_get_globals(va_s66), va_get_reg(EAX, va_s66)) ==
          in_target_slot && TestBit(usbtd_map_get_flags(va_get_globals(va_s66), va_get_reg(EAX,
          va_s66)), USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 713 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        ghost var va_s74, va_c74, va_b74 := va_lemma_block(va_b71, va_s66, va_s65);
        ghost var va_cond_c74, va_s75:va_state := va_lemma_ifElse(va_get_ifCond(va_c74),
          va_get_ifTrue(va_c74), va_get_ifFalse(va_c74), va_s66, va_s74);
        if (va_cond_c74)
        {
          ghost var va_b76 := va_get_block(va_get_ifTrue(va_c74));
          ghost var va_b77, va_s77 := va_lemma_MOV_ToReg(va_b76, va_s75, va_s74,
            va_op_reg_reg(ESI), va_const_word(FALSE));
          va_s74 := va_lemma_empty(va_s77, va_s74);
        }
        else
        {
          ghost var va_b78 := va_get_block(va_get_ifFalse(va_c74));
          ghost var va_b79, va_s79 := va_lemma_ADD(va_b78, va_s75, va_s74, va_op_word_reg(EAX),
            va_const_word(1));
          ghost var va_b80, va_s80 := va_lemma_MOV_ToReg(va_b79, va_s79, va_s74,
            va_op_reg_reg(ESI), va_const_word(TRUE));
          va_s74 := va_lemma_empty(va_s80, va_s74);
        }
        va_s65 := va_lemma_empty(va_s74, va_s65);
      }
      va_s61 := va_lemma_empty(va_s65, va_s61);
    }
    else
    {
      ghost var va_b81 := va_get_block(va_get_ifFalse(va_c61));
      ghost var va_s82, va_c82, va_b82 := va_lemma_block(va_b81, va_s62, va_s61);
      ghost var va_cond_c82, va_s83:va_state := va_lemma_ifElse(va_get_ifCond(va_c82),
        va_get_ifTrue(va_c82), va_get_ifFalse(va_c82), va_s62, va_s82);
      if (va_cond_c82)
      {
        ghost var va_b84 := va_get_block(va_get_ifTrue(va_c82));
        ghost var va_b85, va_s85 := va_lemma_MOV_ToReg(va_b84, va_s83, va_s82, va_op_reg_reg(ESI),
          va_const_word(FALSE));
        assert !(usbtd_map_get_usbpdev_slotid(va_get_globals(va_s85), va_get_reg(EAX, va_s85)) ==
          in_target_slot);  // line 730 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        assert !(usbtd_map_get_usbpdev_slotid(va_get_globals(va_s85), va_get_reg(EAX, va_s85)) ==
          in_target_slot && TestBit(usbtd_map_get_flags(va_get_globals(va_s85), va_get_reg(EAX,
          va_s85)), USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 731 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        va_s82 := va_lemma_empty(va_s85, va_s82);
      }
      else
      {
        ghost var va_b88 := va_get_block(va_get_ifFalse(va_c82));
        assert !(usbtd_map_get_usbpdev_slotid(va_get_globals(va_s83), va_get_reg(EAX, va_s83)) ==
          in_target_slot);  // line 736 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        assert !(usbtd_map_get_usbpdev_slotid(va_get_globals(va_s83), va_get_reg(EAX, va_s83)) ==
          in_target_slot && TestBit(usbtd_map_get_flags(va_get_globals(va_s83), va_get_reg(EAX,
          va_s83)), USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 737 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
        ghost var va_b91, va_s91 := va_lemma_ADD(va_b88, va_s83, va_s82, va_op_word_reg(EAX),
          va_const_word(1));
        ghost var va_b92, va_s92 := va_lemma_MOV_ToReg(va_b91, va_s91, va_s82, va_op_reg_reg(ESI),
          va_const_word(TRUE));
        va_s82 := va_lemma_empty(va_s92, va_s82);
      }
      va_s61 := va_lemma_empty(va_s82, va_s61);
    }
    if (va_get_reg(EBX, va_s61) == FALSE)
    {
      assert !(usbtd_map_get_usbpdev_slotid(va_get_globals(va_s61), cur_i) == in_target_slot &&
        TestBit(usbtd_map_get_flags(va_get_globals(va_s61), cur_i),
        USBTD_SLOT_FLAG_SlotSecure_Bit));  // line 746 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert forall j:uint32 :: 0 <= j < va_get_reg(EAX, va_s61) && usbtd_map_valid_slot_id(j) ==>
        !(usbtd_map_get_usbpdev_slotid(va_get_globals(va_s61), j) == in_target_slot &&
        TestBit(usbtd_map_get_flags(va_get_globals(va_s61), j), USBTD_SLOT_FLAG_SlotSecure_Bit)); 
        // line 749 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    }
    Lemma_modify_regs_stateeq(old_this, va_s61);
    va_sW45 := va_lemma_empty(va_s61, va_sW45);
    va_sW44 := va_sW45;
    va_n44 := va_n44 - 1;
  }
  va_s43 := va_lemma_whileFalse(va_get_whileCond(va_c43), va_get_whileBody(va_c43), va_sW44,
    va_s43);
  assert va_get_reg(ECX, va_s43) == TRUE && va_get_reg(EDX, va_s43) == TRUE <==> va_get_reg(EBX,
    va_s43) == TRUE;  // line 758 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
  ghost var t_ret_ref := va_get_reg(ECX, va_s43);
  ghost var t_ret_flag := va_get_reg(EDX, va_s43);
  ghost var t_found_slot := va_get_reg(EBX, va_s43);
  ghost var va_s99, va_c99, va_b99 := va_lemma_block(va_b43, va_s43, va_sM);
  ghost var va_cond_c99, va_s100:va_state := va_lemma_ifElse(va_get_ifCond(va_c99),
    va_get_ifTrue(va_c99), va_get_ifFalse(va_c99), va_s43, va_s99);
  if (va_cond_c99)
  {
    ghost var va_b101 := va_get_block(va_get_ifTrue(va_c99));
    ghost var va_s102, va_c102, va_b102 := va_lemma_block(va_b101, va_s100, va_s99);
    ghost var va_cond_c102, va_s103:va_state := va_lemma_ifElse(va_get_ifCond(va_c102),
      va_get_ifTrue(va_c102), va_get_ifFalse(va_c102), va_s100, va_s102);
    if (va_cond_c102)
    {
      ghost var va_b104 := va_get_block(va_get_ifTrue(va_c102));
      assert va_get_reg(EBX, va_s103) == TRUE;  // line 766 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      ghost var va_b106, va_s106 := va_lemma_Store(va_b104, va_s103, va_s102, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      ghost var va_b107, va_s107 := va_lemma_Store(va_b106, va_s106, va_s102, va_op_word_reg(EBP),
        2 * ARCH_WORD_BYTES, va_op_word_reg(EAX));
      va_s102 := va_lemma_empty(va_s107, va_s102);
    }
    else
    {
      ghost var va_b108 := va_get_block(va_get_ifFalse(va_c102));
      assert t_ret_ref == va_get_reg(ECX, va_s103);  // line 773 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert t_ret_flag == va_get_reg(EDX, va_s103);  // line 774 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert t_found_slot == va_get_reg(EBX, va_s103);  // line 775 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert va_get_reg(EBX, va_s103) == FALSE;  // line 777 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      assert va_get_reg(EAX, va_s103) == USB_TD_ENTRY_NUM - 1;  // line 778 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
      ghost var va_b114, va_s114 := va_lemma_Store(va_b108, va_s103, va_s102, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b115, va_s115 := va_lemma_Store(va_b114, va_s114, va_s102, va_op_word_reg(EBP),
        2 * ARCH_WORD_BYTES, va_const_word(USBTD_SlotID_INVALID));
      va_s102 := va_lemma_empty(va_s115, va_s102);
    }
    va_s99 := va_lemma_empty(va_s102, va_s99);
  }
  else
  {
    ghost var va_b116 := va_get_block(va_get_ifFalse(va_c99));
    assert t_ret_ref == va_get_reg(ECX, va_s100);  // line 786 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    assert t_ret_flag == va_get_reg(EDX, va_s100);  // line 787 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    assert t_found_slot == va_get_reg(EBX, va_s100);  // line 788 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    assert va_get_reg(EBX, va_s100) == FALSE;  // line 790 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    assert va_get_reg(EAX, va_s100) == USB_TD_ENTRY_NUM - 1;  // line 791 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.private.vad
    ghost var va_b122, va_s122 := va_lemma_Store(va_b116, va_s100, va_s99, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b123, va_s123 := va_lemma_Store(va_b122, va_s122, va_s99, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(USBTD_SlotID_INVALID));
    va_s99 := va_lemma_empty(va_s123, va_s99);
  }
  ghost var va_b124, va_s124 := va_lemma_POP_Reg1ToReg6(va_b99, va_s99, va_sM);
  ghost var va_b125, va_s125 := va_lemma_POP_OneReg(va_b124, va_s124, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s125, va_sM);
}
//--
