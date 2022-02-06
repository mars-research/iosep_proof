include "usb_tds_checks.gen.dfy"
//-- _usbtd_verify_qtd32_step1
//--
//-- _usbtd_verify_qtd32_step2
//--
//-- _usbtd_verify_qtd32_step3
//--
//-- _usbtd_verify_qtd32_step1_to_step4
//--
//-- usbtd_verify_qtd32

function method{:opaque} va_code_usbtd_verify_qtd32():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(TRUE)), va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES), va_CCons(va_code_usbtd_check_td_slot_id(va_op_reg_reg(ESI),
    va_op_reg_reg(EAX)), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(ESI)), va_CCons(va_code_usbtd_get_id(),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(ESI),
    va_const_cmp(USBTD_ID_INVALID)), va_Block(va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(ESI)),
    va_CCons(va_code_usbtd_get_wimpdrv_slotid(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(EBX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_wimpdrv_ops_get_updateflag(), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP),
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI),
    va_const_cmp(WimpDrv_Slot_UpdateFlag_Complete)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code__usbtd_verify_qtd32_step1_to_step4(),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(3
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_CALL_USBTD_CheckNotModifyUSBPDevAddrs(),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil()))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 50} va_lemma_usbtd_verify_qtd32(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_usbtd_verify_qtd32(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 17 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES
    + 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM)); ret
    == TRUE ==> usbtd_map_valid_slot_id(td_slot)
  ensures  var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM)); ret
    == TRUE ==> (var drv_slot := usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s0), td_slot); 0 <=
    drv_slot < WimpDrv_Info_ENTRIES)
  ensures  var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM)); ret
    == TRUE ==> (var drv_slot := usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s0), td_slot);
    WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(va_get_globals(va_s0), drv_slot),
    wimpdrv_do_get_paddr_end(va_get_globals(va_s0), drv_slot)))
  ensures  var drv_id := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var td_slot :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES); var ret:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM)); ret == TRUE ==> (var drv_slot :=
    usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s0), td_slot);
    WK_USBTD_Map_SecureGlobalVarValues_qTD32(va_get_globals(va_s0), td_slot))
  ensures  va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  var stack_params_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_params_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_usbtd_verify_qtd32();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b9, va_s9 := va_lemma_MOV_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EAX),
    va_const_word(TRUE));
  ghost var drv_id := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
  ghost var td_slot := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 1 *
    ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_usbtd_check_td_slot_id(va_b12, va_s12, va_sM,
    va_op_reg_reg(ESI), va_op_reg_reg(EAX));
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_Load(va_b16, va_s15, va_s14, va_op_word_reg(ESI),
      va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
    ghost var va_b18, va_s18 := va_lemma_PUSH(va_b17, va_s17, va_s14, va_op_word_reg(ESI));
    ghost var va_b19, va_s19 := va_lemma_usbtd_get_id(va_b18, va_s18, va_s14);
    ghost var va_b20, va_s20 := va_lemma_Load(va_b19, va_s19, va_s14, va_op_word_reg(ESI),
      va_op_word_reg(ESP), 0);
    ghost var va_b21, va_s21 := va_lemma_POP_VOID(va_b20, va_s20, va_s14, 1 * ARCH_WORD_BYTES);
    ghost var globals1 := va_get_globals(va_s21);
    assert globals1 == va_get_globals(va_old_s);  // line 129 column 9 of file .\dev/usb2/usb_tds_ops/usb_tds_checks_qtd.vad
    ghost var va_s24, va_c24, va_b24 := va_lemma_block(va_b21, va_s21, va_s14);
    ghost var va_cond_c24, va_s25:va_state := va_lemma_ifElse(va_get_ifCond(va_c24),
      va_get_ifTrue(va_c24), va_get_ifFalse(va_c24), va_s21, va_s24);
    if (va_cond_c24)
    {
      ghost var va_b26 := va_get_block(va_get_ifTrue(va_c24));
      ghost var va_b27, va_s27 := va_lemma_Load(va_b26, va_s25, va_s24, va_op_word_reg(ESI),
        va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
      ghost var va_b28, va_s28 := va_lemma_PUSH(va_b27, va_s27, va_s24, va_op_word_reg(ESI));
      ghost var va_b29, va_s29 := va_lemma_usbtd_get_wimpdrv_slotid(va_b28, va_s28, va_s24);
      ghost var va_b30, va_s30 := va_lemma_Load(va_b29, va_s29, va_s24, va_op_word_reg(EBX),
        va_op_word_reg(ESP), 0);
      ghost var va_b31, va_s31 := va_lemma_POP_VOID(va_b30, va_s30, va_s24, 1 * ARCH_WORD_BYTES);
      ghost var va_b32, va_s32 := va_lemma_wimpdrv_check_slotid(va_b31, va_s31, va_s24,
        va_op_reg_reg(EBX), va_op_reg_reg(EAX));
      ghost var globals2 := va_get_globals(va_s32);
      assert globals2 == va_get_globals(va_old_s);  // line 142 column 13 of file .\dev/usb2/usb_tds_ops/usb_tds_checks_qtd.vad
      ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b32, va_s32, va_s24);
      ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
        va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s32, va_s35);
      if (va_cond_c35)
      {
        ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
        ghost var va_b38, va_s38 := va_lemma_Load(va_b37, va_s36, va_s35, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
        ghost var va_b39, va_s39 := va_lemma_PUSH(va_b38, va_s38, va_s35, va_op_word_reg(EDI));
        ghost var va_b40, va_s40 := va_lemma_PUSH(va_b39, va_s39, va_s35, va_op_word_reg(EBX));
        ghost var va_b41, va_s41 := va_lemma_wimpdrv_ops_get_updateflag(va_b40, va_s40, va_s35);
        ghost var va_b42, va_s42 := va_lemma_Load(va_b41, va_s41, va_s35, va_op_word_reg(ESI),
          va_op_word_reg(ESP), 0);
        ghost var va_b43, va_s43 := va_lemma_Load(va_b42, va_s42, va_s35, va_op_word_reg(EDI),
          va_op_word_reg(ESP), ARCH_WORD_BYTES);
        ghost var va_b44, va_s44 := va_lemma_POP_VOID(va_b43, va_s43, va_s35, 2 * ARCH_WORD_BYTES);
        ghost var globals3 := va_get_globals(va_s44);
        assert globals3 == va_get_globals(va_old_s);  // line 155 column 17 of file .\dev/usb2/usb_tds_ops/usb_tds_checks_qtd.vad
        ghost var va_s47, va_c47, va_b47 := va_lemma_block(va_b44, va_s44, va_s35);
        ghost var va_cond_c47, va_s48:va_state := va_lemma_ifElse(va_get_ifCond(va_c47),
          va_get_ifTrue(va_c47), va_get_ifFalse(va_c47), va_s44, va_s47);
        if (va_cond_c47)
        {
          ghost var va_b49 := va_get_block(va_get_ifTrue(va_c47));
          ghost var va_s50, va_c50, va_b50 := va_lemma_block(va_b49, va_s48, va_s47);
          ghost var va_cond_c50, va_s51:va_state := va_lemma_ifElse(va_get_ifCond(va_c50),
            va_get_ifTrue(va_c50), va_get_ifFalse(va_c50), va_s48, va_s50);
          if (va_cond_c50)
          {
            ghost var va_b52 := va_get_block(va_get_ifTrue(va_c50));
            ghost var va_b53, va_s53 := va_lemma_Load(va_b52, va_s51, va_s50, va_op_word_reg(EDI),
              va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
            ghost var va_b54, va_s54 := va_lemma_PUSH(va_b53, va_s53, va_s50, va_op_word_reg(EDI));
            ghost var va_b55, va_s55 := va_lemma_Load(va_b54, va_s54, va_s50, va_op_word_reg(EDI),
              va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
            ghost var va_b56, va_s56 := va_lemma_PUSH(va_b55, va_s55, va_s50, va_op_word_reg(EDI));
            ghost var va_b57, va_s57 := va_lemma_PUSH(va_b56, va_s56, va_s50, va_op_word_reg(EBX));
            ghost var va_b58, va_s58 := va_lemma__usbtd_verify_qtd32_step1_to_step4(va_b57, va_s57,
              va_s50);
            ghost var va_b59, va_s59 := va_lemma_Load(va_b58, va_s58, va_s50, va_op_word_reg(ESI),
              va_op_word_reg(ESP), 0);
            ghost var va_b60, va_s60 := va_lemma_POP_VOID(va_b59, va_s59, va_s50, 3 *
              ARCH_WORD_BYTES);
            ghost var globals4 := va_get_globals(va_s60);
            assert globals4 == va_get_globals(va_old_s);  // line 170 column 25 of file .\dev/usb2/usb_tds_ops/usb_tds_checks_qtd.vad
            ghost var va_s63, va_c63, va_b63 := va_lemma_block(va_b60, va_s60, va_s50);
            ghost var va_cond_c63, va_s64:va_state := va_lemma_ifElse(va_get_ifCond(va_c63),
              va_get_ifTrue(va_c63), va_get_ifFalse(va_c63), va_s60, va_s63);
            if (va_cond_c63)
            {
              ghost var va_b65 := va_get_block(va_get_ifTrue(va_c63));
              ghost var va_b66, va_s66 := va_lemma_Load(va_b65, va_s64, va_s63,
                va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
              ghost var va_b67, va_s67 := va_lemma_PUSH(va_b66, va_s66, va_s63,
                va_op_word_reg(EDI));
              ghost var va_b68, va_s68 := va_lemma_CALL_USBTD_CheckNotModifyUSBPDevAddrs(va_b67,
                va_s67, va_s63);
              ghost var globals5 := va_get_globals(va_s68);
              ghost var va_b70, va_s70 := va_lemma_Load(va_b68, va_s68, va_s63,
                va_op_word_reg(ESI), va_op_word_reg(ESP), 0);
              ghost var va_b71, va_s71 := va_lemma_POP_VOID(va_b70, va_s70, va_s63, 1 *
                ARCH_WORD_BYTES);
              ghost var va_s72, va_c72, va_b72 := va_lemma_block(va_b71, va_s71, va_s63);
              ghost var va_cond_c72, va_s73:va_state := va_lemma_ifElse(va_get_ifCond(va_c72),
                va_get_ifTrue(va_c72), va_get_ifFalse(va_c72), va_s71, va_s72);
              if (va_cond_c72)
              {
                ghost var va_b74 := va_get_block(va_get_ifTrue(va_c72));
                assert Is_USBTD_NotModifyUSBPDevsAddrs(globals5, td_slot);  // line 184 column 33 of file .\dev/usb2/usb_tds_ops/usb_tds_checks_qtd.vad
                assert Is_USBTD_NotModifyUSBPDevsAddrs(va_get_globals(va_old_s), td_slot);  // line 185 column 33 of file .\dev/usb2/usb_tds_ops/usb_tds_checks_qtd.vad
                ghost var va_b77, va_s77 := va_lemma_Store(va_b74, va_s73, va_s72,
                  va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE));
                va_s72 := va_lemma_empty(va_s77, va_s72);
              }
              else
              {
                ghost var va_b78 := va_get_block(va_get_ifFalse(va_c72));
                ghost var va_b79, va_s79 := va_lemma_Store(va_b78, va_s73, va_s72,
                  va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE));
                va_s72 := va_lemma_empty(va_s79, va_s72);
              }
              va_s63 := va_lemma_empty(va_s72, va_s63);
            }
            else
            {
              ghost var va_b80 := va_get_block(va_get_ifFalse(va_c63));
              ghost var va_b81, va_s81 := va_lemma_Store(va_b80, va_s64, va_s63,
                va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE));
              va_s63 := va_lemma_empty(va_s81, va_s63);
            }
            va_s50 := va_lemma_empty(va_s63, va_s50);
          }
          else
          {
            ghost var va_b82 := va_get_block(va_get_ifFalse(va_c50));
            ghost var va_b83, va_s83 := va_lemma_Store(va_b82, va_s51, va_s50, va_op_word_reg(EBP),
              ARCH_WORD_BYTES, va_const_word(FALSE));
            va_s50 := va_lemma_empty(va_s83, va_s50);
          }
          va_s47 := va_lemma_empty(va_s50, va_s47);
        }
        else
        {
          ghost var va_b84 := va_get_block(va_get_ifFalse(va_c47));
          ghost var va_b85, va_s85 := va_lemma_Store(va_b84, va_s48, va_s47, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          va_s47 := va_lemma_empty(va_s85, va_s47);
        }
        va_s35 := va_lemma_empty(va_s47, va_s35);
      }
      else
      {
        ghost var va_b86 := va_get_block(va_get_ifFalse(va_c35));
        ghost var va_b87, va_s87 := va_lemma_Store(va_b86, va_s36, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        va_s35 := va_lemma_empty(va_s87, va_s35);
      }
      va_s24 := va_lemma_empty(va_s35, va_s24);
    }
    else
    {
      ghost var va_b88 := va_get_block(va_get_ifFalse(va_c24));
      ghost var va_b89, va_s89 := va_lemma_Store(va_b88, va_s25, va_s24, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      va_s24 := va_lemma_empty(va_s89, va_s24);
    }
    va_s14 := va_lemma_empty(va_s24, va_s14);
  }
  else
  {
    ghost var va_b90 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b91, va_s91 := va_lemma_Store(va_b90, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s14 := va_lemma_empty(va_s91, va_s14);
  }
  ghost var va_b92, va_s92 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b93, va_s93 := va_lemma_POP_OneReg(va_b92, va_s92, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s93, va_sM);
}
//--
//-- _usbtd_verify_qtd32_step1

function method{:opaque} va_code__usbtd_verify_qtd32_step1():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_usbtd_get_td_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(ESI), va_const_cmp(PID_INVALID)),
    va_Block(va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(ESI),
    va_const_cmp(PID_RESERVED_OS_PARTITION)), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(TRUE)), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))
}

lemma va_lemma__usbtd_verify_qtd32_step1(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbtd_verify_qtd32_step1(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 3 * ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var drv_pid := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var td_slot :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES); var ret:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM)); ret == TRUE ==>
    p__usbtd_verify_qtd32_step1_OnSuccessCheck(va_get_globals(va_s0), drv_pid, td_slot)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  var stack_params_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_params_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(EBP,
    va_sM, va_update_reg(ESP, va_sM, va_update_ok(va_sM, va_s0)))))))))
{
  reveal_va_code__usbtd_verify_qtd32_step1();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_p__usbtd_verify_qtd32_step1_OnSuccessCheck();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b4, va_s4, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b8, va_s8 := va_lemma_Load(va_b7, va_s7, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b9, va_s9 := va_lemma_Load(va_b8, va_s8, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b10, va_s10 := va_lemma_PUSH(va_b9, va_s9, va_sM, va_op_word_reg(EDI));
  ghost var va_b11, va_s11 := va_lemma_usbtd_get_td_pid(va_b10, va_s10, va_sM);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0);
  ghost var va_b13, va_s13 := va_lemma_POP_VOID(va_b12, va_s12, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_s17, va_c17, va_b17 := va_lemma_block(va_b16, va_s15, va_s14);
    ghost var va_cond_c17, va_s18:va_state := va_lemma_ifElse(va_get_ifCond(va_c17),
      va_get_ifTrue(va_c17), va_get_ifFalse(va_c17), va_s15, va_s17);
    if (va_cond_c17)
    {
      ghost var va_b19 := va_get_block(va_get_ifTrue(va_c17));
      ghost var va_s20, va_c20, va_b20 := va_lemma_block(va_b19, va_s18, va_s17);
      ghost var va_cond_c20, va_s21:va_state := va_lemma_ifElse(va_get_ifCond(va_c20),
        va_get_ifTrue(va_c20), va_get_ifFalse(va_c20), va_s18, va_s20);
      if (va_cond_c20)
      {
        ghost var va_b22 := va_get_block(va_get_ifTrue(va_c20));
        ghost var va_b23, va_s23 := va_lemma_Store(va_b22, va_s21, va_s20, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(TRUE));
        va_s20 := va_lemma_empty(va_s23, va_s20);
      }
      else
      {
        ghost var va_b24 := va_get_block(va_get_ifFalse(va_c20));
        ghost var va_b25, va_s25 := va_lemma_Store(va_b24, va_s21, va_s20, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        va_s20 := va_lemma_empty(va_s25, va_s20);
      }
      va_s17 := va_lemma_empty(va_s20, va_s17);
    }
    else
    {
      ghost var va_b26 := va_get_block(va_get_ifFalse(va_c17));
      ghost var va_b27, va_s27 := va_lemma_Store(va_b26, va_s18, va_s17, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      va_s17 := va_lemma_empty(va_s27, va_s17);
    }
    va_s14 := va_lemma_empty(va_s17, va_s14);
  }
  else
  {
    ghost var va_b28 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b29, va_s29 := va_lemma_Store(va_b28, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s14 := va_lemma_empty(va_s29, va_s14);
  }
  ghost var va_b30, va_s30 := va_lemma_POP_TwoRegs(va_b14, va_s14, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b31, va_s31 := va_lemma_POP_OneReg(va_b30, va_s30, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s31, va_sM);
}
//--
//-- _usbtd_verify_qtd32_step2

function method{:opaque} va_code__usbtd_verify_qtd32_step2():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID((FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords - 1) * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(ESI)),
    va_CCons(va_code_CALL_USBTD_QTD32_ParseTDPointers(),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX), va_const_word(TRUE)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(ESP), 0),
    va_CCons(va_code_usbtd_verify_td32_check_next_slot_and_tflag(va_op_reg_reg(ESI),
    va_op_reg_reg(EDI), va_op_reg_reg(EDX), va_op_reg_reg(EBX)),
    va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EBX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CNil())), va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 3 *
    ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(ESP),
    ARCH_WORD_BYTES),
    va_CCons(va_code_usbtd_verify_td32_check_next_slot_and_tflag(va_op_reg_reg(ESI),
    va_op_reg_reg(EDI), va_op_reg_reg(EDX), va_op_reg_reg(EBX)),
    va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EBX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CNil())), va_CCons(va_code_POP_VOID(FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords *
    ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))))))
}

lemma{:timeLimitMultiplier 10} va_lemma__usbtd_verify_qtd32_step2(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbtd_verify_qtd32_step2(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 10 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ +
    FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var drv_pid := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var td_slot :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES); var ret:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM)); ret == TRUE ==>
    p__usbtd_verify_qtd32_step2_OnSuccessCheck(va_get_globals(va_s0), drv_pid, td_slot)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  var stack_params_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_params_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code__usbtd_verify_qtd32_step2();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_p_ffi_usbtd_qtd32_parseTDPtrs_retval();
  reveal_p__usbtd_verify_qtd32_step2_OnSuccessCheck();
  ghost var va_b4, va_s4 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b5, va_s5 := va_lemma_MOV_ToReg(va_b4, va_s4, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b11, va_s11 := va_lemma_PUSH_Reg1ToReg6(va_b5, va_s5, va_sM);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var td_slot := va_get_reg(ESI, va_s12);
  ghost var va_b14, va_s14 := va_lemma_PUSH_VOID(va_b12, va_s12, va_sM,
    (FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords - 1) * ARCH_WORD_BYTES);
  ghost var va_b15, va_s15 := va_lemma_PUSH(va_b14, va_s14, va_sM, va_op_word_reg(ESI));
  ghost var va_b16, va_s16 := va_lemma_CALL_USBTD_QTD32_ParseTDPointers(va_b15, va_s15, va_sM);
  ghost var va_b17, va_s17 := va_lemma_MOV_ToReg(va_b16, va_s16, va_sM, va_op_reg_reg(EAX),
    va_const_word(TRUE));
  ghost var va_b18, va_s18 := va_lemma_Load(va_b17, va_s17, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var drv_pid := va_get_reg(ESI, va_s18);
  ghost var va_b20, va_s20 := va_lemma_Load(va_b18, va_s18, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 2 * ARCH_WORD_BYTES);
  ghost var va_b21, va_s21 := va_lemma_Load(va_b20, va_s20, va_sM, va_op_word_reg(EDX),
    va_op_word_reg(ESP), 0);
  ghost var va_b22, va_s22 := va_lemma_usbtd_verify_td32_check_next_slot_and_tflag(va_b21, va_s21,
    va_sM, va_op_reg_reg(ESI), va_op_reg_reg(EDI), va_op_reg_reg(EDX), va_op_reg_reg(EBX));
  ghost var va_s23, va_c23, va_b23 := va_lemma_block(va_b22, va_s22, va_sM);
  ghost var va_cond_c23, va_s24:va_state := va_lemma_ifElse(va_get_ifCond(va_c23),
    va_get_ifTrue(va_c23), va_get_ifFalse(va_c23), va_s22, va_s23);
  if (va_cond_c23)
  {
    ghost var va_b25 := va_get_block(va_get_ifTrue(va_c23));
    ghost var va_b26, va_s26 := va_lemma_MOV_ToReg(va_b25, va_s24, va_s23, va_op_reg_reg(EAX),
      va_const_word(FALSE));
    va_s23 := va_lemma_empty(va_s26, va_s23);
  }
  else
  {
    ghost var va_b27 := va_get_block(va_get_ifFalse(va_c23));
    va_s23 := va_lemma_empty(va_s24, va_s23);
  }
  ghost var va_b28, va_s28 := va_lemma_Load(va_b23, va_s23, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 3 * ARCH_WORD_BYTES);
  ghost var va_b29, va_s29 := va_lemma_Load(va_b28, va_s28, va_sM, va_op_word_reg(EDX),
    va_op_word_reg(ESP), ARCH_WORD_BYTES);
  ghost var va_b30, va_s30 := va_lemma_usbtd_verify_td32_check_next_slot_and_tflag(va_b29, va_s29,
    va_sM, va_op_reg_reg(ESI), va_op_reg_reg(EDI), va_op_reg_reg(EDX), va_op_reg_reg(EBX));
  ghost var va_s31, va_c31, va_b31 := va_lemma_block(va_b30, va_s30, va_sM);
  ghost var va_cond_c31, va_s32:va_state := va_lemma_ifElse(va_get_ifCond(va_c31),
    va_get_ifTrue(va_c31), va_get_ifFalse(va_c31), va_s30, va_s31);
  if (va_cond_c31)
  {
    ghost var va_b33 := va_get_block(va_get_ifTrue(va_c31));
    ghost var va_b34, va_s34 := va_lemma_MOV_ToReg(va_b33, va_s32, va_s31, va_op_reg_reg(EAX),
      va_const_word(FALSE));
    va_s31 := va_lemma_empty(va_s34, va_s31);
  }
  else
  {
    ghost var va_b35 := va_get_block(va_get_ifFalse(va_c31));
    va_s31 := va_lemma_empty(va_s32, va_s31);
  }
  ghost var va_b36, va_s36 := va_lemma_POP_VOID(va_b31, va_s31, va_sM,
    FFI_USBTD_Qtd32_ParseTDPtrs_ReturnWords * ARCH_WORD_BYTES);
  ghost var va_s37, va_c37, va_b37 := va_lemma_block(va_b36, va_s36, va_sM);
  ghost var va_cond_c37, va_s38:va_state := va_lemma_ifElse(va_get_ifCond(va_c37),
    va_get_ifTrue(va_c37), va_get_ifFalse(va_c37), va_s36, va_s37);
  if (va_cond_c37)
  {
    ghost var va_b39 := va_get_block(va_get_ifTrue(va_c37));
    ghost var va_b40, va_s40 := va_lemma_Store(va_b39, va_s38, va_s37, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    va_s37 := va_lemma_empty(va_s40, va_s37);
  }
  else
  {
    ghost var va_b41 := va_get_block(va_get_ifFalse(va_c37));
    ghost var va_b42, va_s42 := va_lemma_Store(va_b41, va_s38, va_s37, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s37 := va_lemma_empty(va_s42, va_s37);
  }
  ghost var va_b43, va_s43 := va_lemma_POP_Reg1ToReg6(va_b37, va_s37, va_sM);
  ghost var va_b44, va_s44 := va_lemma_POP_OneReg(va_b43, va_s43, va_sM, va_op_reg_reg(EBP));
  Lemma_modify_regs_stateeq(va_old_s, va_s44);
  va_sM := va_lemma_empty(va_s44, va_sM);
}
//--
//-- _usbtd_verify_qtd32_step3

function method{:opaque} va_code__usbtd_verify_qtd32_step3():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX),
    va_const_word(TRUE)), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(ECX)), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_wimpdrv_ops_get_do_paddr_region(), va_CCons(va_code_Load(va_op_word_reg(EDX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), 2 *
    ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP),
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(3 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID((FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords - 1) *
    ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(ESI)),
    va_CCons(va_code_CALL_USBTD_QTD32_ParseBufPointers(),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(ESP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_POP_VOID(FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_PUSH(va_op_word_reg(ESI)),
    va_CCons(va_code_usbtd_verify_td32_Check5BufPAddrRange(),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(7
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil())))))))))))))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))
}

lemma{:timeLimitMultiplier 40} va_lemma__usbtd_verify_qtd32_step3(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbtd_verify_qtd32_step3(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires var drv_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= drv_slot
    < WimpDrv_Info_ENTRIES && wimpdrv_do_get_flag(va_get_globals(va_s0), drv_slot) ==
    WimpDrv_Slot_UpdateFlag_Complete
  requires var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var drv_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(va_get_globals(va_s0), drv_slot); var
    wimpdrv_do_pend := wimpdrv_do_get_paddr_end(va_get_globals(va_s0), drv_slot); var ret:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM)); ret == TRUE ==> wimpdrv_do_pbase <=
    wimpdrv_do_pend
  ensures  var drv_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var drv_id :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES); var td_slot :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES); var ret:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM)); ret == TRUE ==>
    p__usbtd_verify_qtd32_step3_OnSuccessCheck(va_get_globals(va_s0), drv_slot, td_slot)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  var stack_params_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_params_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code__usbtd_verify_qtd32_step3();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_p_ffi_usbtd_qtd32_parseDataBufPtrs_retval();
  reveal_p__usbtd_verify_qtd32_step3_OnSuccessCheck();
  ghost var va_b4, va_s4 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b5, va_s5 := va_lemma_MOV_ToReg(va_b4, va_s4, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b12, va_s12 := va_lemma_PUSH_Reg1ToReg6(va_b5, va_s5, va_sM);
  ghost var va_b13, va_s13 := va_lemma_MOV_ToReg(va_b12, va_s12, va_sM, va_op_reg_reg(EAX),
    va_const_word(TRUE));
  ghost var va_b14, va_s14 := va_lemma_PUSH_VOID(va_b13, va_s13, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b15, va_s15 := va_lemma_Load(va_b14, va_s14, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b16, va_s16 := va_lemma_PUSH(va_b15, va_s15, va_sM, va_op_word_reg(ECX));
  ghost var drv_id := va_get_reg(ECX, va_s16);
  ghost var va_b18, va_s18 := va_lemma_Load(va_b16, va_s16, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b19, va_s19 := va_lemma_PUSH(va_b18, va_s18, va_sM, va_op_word_reg(ECX));
  ghost var drv_slot := va_get_reg(ECX, va_s19);
  ghost var va_b21, va_s21 := va_lemma_wimpdrv_ops_get_do_paddr_region(va_b19, va_s19, va_sM);
  ghost var va_b22, va_s22 := va_lemma_Load(va_b21, va_s21, va_sM, va_op_word_reg(EDX),
    va_op_word_reg(ESP), 0);
  ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(ESP), 2 * ARCH_WORD_BYTES);
  ghost var va_b24, va_s24 := va_lemma_Load(va_b23, va_s23, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(ESP), ARCH_WORD_BYTES);
  ghost var va_b25, va_s25 := va_lemma_POP_VOID(va_b24, va_s24, va_sM, 3 * ARCH_WORD_BYTES);
  ghost var va_s26, va_c26, va_b26 := va_lemma_block(va_b25, va_s25, va_sM);
  ghost var va_cond_c26, va_s27:va_state := va_lemma_ifElse(va_get_ifCond(va_c26),
    va_get_ifTrue(va_c26), va_get_ifFalse(va_c26), va_s25, va_s26);
  if (va_cond_c26)
  {
    ghost var va_b28 := va_get_block(va_get_ifTrue(va_c26));
    ghost var va_b29, va_s29 := va_lemma_PUSH(va_b28, va_s27, va_s26, va_op_word_reg(ECX));
    ghost var va_b30, va_s30 := va_lemma_PUSH(va_b29, va_s29, va_s26, va_op_word_reg(EBX));
    ghost var va_b31, va_s31 := va_lemma_Load(va_b30, va_s30, va_s26, va_op_word_reg(ESI),
      va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
    ghost var td_slot := va_get_reg(ESI, va_s31);
    ghost var va_b33, va_s33 := va_lemma_PUSH_VOID(va_b31, va_s31, va_s26,
      (FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords - 1) * ARCH_WORD_BYTES);
    ghost var va_b34, va_s34 := va_lemma_PUSH(va_b33, va_s33, va_s26, va_op_word_reg(ESI));
    ghost var va_b35, va_s35 := va_lemma_CALL_USBTD_QTD32_ParseBufPointers(va_b34, va_s34, va_s26);
    ghost var va_b36, va_s36 := va_lemma_Load(va_b35, va_s35, va_s26, va_op_word_reg(ESI),
      va_op_word_reg(ESP), 0);
    ghost var va_b37, va_s37 := va_lemma_Load(va_b36, va_s36, va_s26, va_op_word_reg(EDI),
      va_op_word_reg(ESP), 1 * ARCH_WORD_BYTES);
    ghost var va_b38, va_s38 := va_lemma_Load(va_b37, va_s37, va_s26, va_op_word_reg(EDX),
      va_op_word_reg(ESP), 2 * ARCH_WORD_BYTES);
    ghost var va_b39, va_s39 := va_lemma_Load(va_b38, va_s38, va_s26, va_op_word_reg(ECX),
      va_op_word_reg(ESP), 3 * ARCH_WORD_BYTES);
    ghost var va_b40, va_s40 := va_lemma_Load(va_b39, va_s39, va_s26, va_op_word_reg(EBX),
      va_op_word_reg(ESP), 4 * ARCH_WORD_BYTES);
    ghost var va_b41, va_s41 := va_lemma_POP_VOID(va_b40, va_s40, va_s26,
      FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES);
    ghost var va_b42, va_s42 := va_lemma_PUSH(va_b41, va_s41, va_s26, va_op_word_reg(EBX));
    ghost var va_b43, va_s43 := va_lemma_PUSH(va_b42, va_s42, va_s26, va_op_word_reg(ECX));
    ghost var va_b44, va_s44 := va_lemma_PUSH(va_b43, va_s43, va_s26, va_op_word_reg(EDX));
    ghost var va_b45, va_s45 := va_lemma_PUSH(va_b44, va_s44, va_s26, va_op_word_reg(EDI));
    ghost var va_b46, va_s46 := va_lemma_PUSH(va_b45, va_s45, va_s26, va_op_word_reg(ESI));
    ghost var va_b47, va_s47 := va_lemma_usbtd_verify_td32_Check5BufPAddrRange(va_b46, va_s46,
      va_s26);
    ghost var va_b48, va_s48 := va_lemma_Load(va_b47, va_s47, va_s26, va_op_word_reg(EDX),
      va_op_word_reg(ESP), 0);
    ghost var va_b49, va_s49 := va_lemma_POP_VOID(va_b48, va_s48, va_s26, 7 * ARCH_WORD_BYTES);
    ghost var va_s50, va_c50, va_b50 := va_lemma_block(va_b49, va_s49, va_s26);
    ghost var va_cond_c50, va_s51:va_state := va_lemma_ifElse(va_get_ifCond(va_c50),
      va_get_ifTrue(va_c50), va_get_ifFalse(va_c50), va_s49, va_s50);
    if (va_cond_c50)
    {
      ghost var va_b52 := va_get_block(va_get_ifTrue(va_c50));
      ghost var va_b53, va_s53 := va_lemma_Store(va_b52, va_s51, va_s50, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      va_s50 := va_lemma_empty(va_s53, va_s50);
    }
    else
    {
      ghost var va_b54 := va_get_block(va_get_ifFalse(va_c50));
      ghost var va_b55, va_s55 := va_lemma_Store(va_b54, va_s51, va_s50, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      va_s50 := va_lemma_empty(va_s55, va_s50);
    }
    va_s26 := va_lemma_empty(va_s50, va_s26);
  }
  else
  {
    ghost var va_b56 := va_get_block(va_get_ifFalse(va_c26));
    ghost var va_b57, va_s57 := va_lemma_Store(va_b56, va_s27, va_s26, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s26 := va_lemma_empty(va_s57, va_s26);
  }
  ghost var va_b58, va_s58 := va_lemma_POP_Reg1ToReg6(va_b26, va_s26, va_sM);
  ghost var va_b59, va_s59 := va_lemma_POP_OneReg(va_b58, va_s58, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s59, va_sM);
}
//--
//-- _usbtd_verify_qtd32_step1_to_step4

function method{:opaque} va_code__usbtd_verify_qtd32_step1_to_step4():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX), va_const_word(TRUE)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_wimpdrv_ops_get_pid(), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP),
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(ESI)), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code__usbtd_verify_qtd32_step1(), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(ESI)), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code__usbtd_verify_qtd32_step2(), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code__usbtd_verify_qtd32_step3(),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(3
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_usbtd_get_usbpdev_slotid(),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI),
    va_const_cmp(WimpUSBPDev_SlotID_EMPTY)), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(TRUE)), va_CNil())),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ESI), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))
}

lemma{:timeLimitMultiplier 50} va_lemma__usbtd_verify_qtd32_step1_to_step4(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbtd_verify_qtd32_step1_to_step4(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 10 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + FFI_USBTD_Qtd32_ParseDataBufPtrs_ReturnWords * ARCH_WORD_BYTES
    + 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var
    stack_params_space := 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires var drv_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); 0 <= drv_slot
    < WimpDrv_Info_ENTRIES && wimpdrv_do_get_flag(va_get_globals(va_s0), drv_slot) ==
    WimpDrv_Slot_UpdateFlag_Complete
  requires var td_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); usbtd_map_valid_slot_id(td_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var drv_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var td_slot :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES); var ret:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM)); ret == TRUE ==>
    WK_ValidPMemRegion(wimpdrv_do_get_paddr_base(va_get_globals(va_s0), drv_slot),
    wimpdrv_do_get_paddr_end(va_get_globals(va_s0), drv_slot))
  ensures  var drv_slot := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var drv_id :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES); var td_slot :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES); var ret:word :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_sM)); (((ret == TRUE ==>
    p__usbtd_verify_qtd32_step1_OnSuccessCheck(va_get_globals(va_s0),
    wimpdrv_get_pid(va_get_globals(va_s0), drv_slot).v, td_slot)) && (ret == TRUE ==>
    p__usbtd_verify_qtd32_step2_OnSuccessCheck(va_get_globals(va_s0),
    wimpdrv_get_pid(va_get_globals(va_s0), drv_slot).v, td_slot))) && (ret == TRUE ==>
    p__usbtd_verify_qtd32_step3_OnSuccessCheck(va_get_globals(va_s0), drv_slot, td_slot))) && (ret
    == TRUE ==> p__usbtd_verify_qtd32_step4_OnSuccessCheck(va_get_globals(va_s0), td_slot))
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  var stack_params_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_params_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code__usbtd_verify_qtd32_step1_to_step4();
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
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(EAX));
  ghost var va_b9, va_s9 := va_lemma_MOV_ToReg(va_b8, va_s8, va_sM, va_op_reg_reg(EAX),
    va_const_word(TRUE));
  ghost var drv_slot := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
  ghost var drv_id := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 1 *
    ARCH_WORD_BYTES);
  ghost var td_slot := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s) + 2 *
    ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b14, va_s14 := va_lemma_PUSH(va_b13, va_s13, va_sM, va_op_word_reg(EDI));
  ghost var va_b15, va_s15 := va_lemma_Load(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b16, va_s16 := va_lemma_PUSH(va_b15, va_s15, va_sM, va_op_word_reg(EDI));
  ghost var va_b17, va_s17 := va_lemma_wimpdrv_ops_get_pid(va_b16, va_s16, va_sM);
  ghost var va_b18, va_s18 := va_lemma_Load(va_b17, va_s17, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(ESP), 0);
  ghost var va_b19, va_s19 := va_lemma_Load(va_b18, va_s18, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), ARCH_WORD_BYTES);
  ghost var va_b20, va_s20 := va_lemma_POP_VOID(va_b19, va_s19, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s21, va_c21, va_b21 := va_lemma_block(va_b20, va_s20, va_sM);
  ghost var va_cond_c21, va_s22:va_state := va_lemma_ifElse(va_get_ifCond(va_c21),
    va_get_ifTrue(va_c21), va_get_ifFalse(va_c21), va_s20, va_s21);
  if (va_cond_c21)
  {
    ghost var va_b23 := va_get_block(va_get_ifTrue(va_c21));
    ghost var va_b24, va_s24 := va_lemma_Load(va_b23, va_s22, va_s21, va_op_word_reg(ESI),
      va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
    ghost var va_b25, va_s25 := va_lemma_PUSH(va_b24, va_s24, va_s21, va_op_word_reg(ESI));
    ghost var va_b26, va_s26 := va_lemma_PUSH(va_b25, va_s25, va_s21, va_op_word_reg(EDI));
    ghost var va_b27, va_s27 := va_lemma__usbtd_verify_qtd32_step1(va_b26, va_s26, va_s21);
    ghost var va_b28, va_s28 := va_lemma_Load(va_b27, va_s27, va_s21, va_op_word_reg(ESI),
      va_op_word_reg(ESP), 0);
    ghost var va_b29, va_s29 := va_lemma_POP_VOID(va_b28, va_s28, va_s21, 2 * ARCH_WORD_BYTES);
    ghost var va_s30, va_c30, va_b30 := va_lemma_block(va_b29, va_s29, va_s21);
    ghost var va_cond_c30, va_s31:va_state := va_lemma_ifElse(va_get_ifCond(va_c30),
      va_get_ifTrue(va_c30), va_get_ifFalse(va_c30), va_s29, va_s30);
    if (va_cond_c30)
    {
      ghost var va_b32 := va_get_block(va_get_ifTrue(va_c30));
      ghost var va_b33, va_s33 := va_lemma_Load(va_b32, va_s31, va_s30, va_op_word_reg(ESI),
        va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
      ghost var va_b34, va_s34 := va_lemma_PUSH(va_b33, va_s33, va_s30, va_op_word_reg(ESI));
      ghost var va_b35, va_s35 := va_lemma_PUSH(va_b34, va_s34, va_s30, va_op_word_reg(EDI));
      ghost var va_b36, va_s36 := va_lemma__usbtd_verify_qtd32_step2(va_b35, va_s35, va_s30);
      ghost var va_b37, va_s37 := va_lemma_Load(va_b36, va_s36, va_s30, va_op_word_reg(ESI),
        va_op_word_reg(ESP), 0);
      ghost var va_b38, va_s38 := va_lemma_POP_VOID(va_b37, va_s37, va_s30, 2 * ARCH_WORD_BYTES);
      ghost var va_s39, va_c39, va_b39 := va_lemma_block(va_b38, va_s38, va_s30);
      ghost var va_cond_c39, va_s40:va_state := va_lemma_ifElse(va_get_ifCond(va_c39),
        va_get_ifTrue(va_c39), va_get_ifFalse(va_c39), va_s38, va_s39);
      if (va_cond_c39)
      {
        ghost var va_b41 := va_get_block(va_get_ifTrue(va_c39));
        ghost var va_b42, va_s42 := va_lemma_Load(va_b41, va_s40, va_s39, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
        ghost var va_b43, va_s43 := va_lemma_PUSH(va_b42, va_s42, va_s39, va_op_word_reg(EDI));
        ghost var va_b44, va_s44 := va_lemma_Load(va_b43, va_s43, va_s39, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
        ghost var va_b45, va_s45 := va_lemma_PUSH(va_b44, va_s44, va_s39, va_op_word_reg(EDI));
        ghost var va_b46, va_s46 := va_lemma_Load(va_b45, va_s45, va_s39, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
        ghost var va_b47, va_s47 := va_lemma_PUSH(va_b46, va_s46, va_s39, va_op_word_reg(EDI));
        ghost var va_b48, va_s48 := va_lemma__usbtd_verify_qtd32_step3(va_b47, va_s47, va_s39);
        ghost var va_b49, va_s49 := va_lemma_Load(va_b48, va_s48, va_s39, va_op_word_reg(ESI),
          va_op_word_reg(ESP), 0);
        ghost var va_b50, va_s50 := va_lemma_POP_VOID(va_b49, va_s49, va_s39, 3 * ARCH_WORD_BYTES);
        ghost var va_s51, va_c51, va_b51 := va_lemma_block(va_b50, va_s50, va_s39);
        ghost var va_cond_c51, va_s52:va_state := va_lemma_ifElse(va_get_ifCond(va_c51),
          va_get_ifTrue(va_c51), va_get_ifFalse(va_c51), va_s50, va_s51);
        if (va_cond_c51)
        {
          ghost var va_b53 := va_get_block(va_get_ifTrue(va_c51));
          ghost var va_b54, va_s54 := va_lemma_Load(va_b53, va_s52, va_s51, va_op_word_reg(EDI),
            va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
          ghost var va_b55, va_s55 := va_lemma_PUSH(va_b54, va_s54, va_s51, va_op_word_reg(EDI));
          ghost var va_b56, va_s56 := va_lemma_usbtd_get_usbpdev_slotid(va_b55, va_s55, va_s51);
          ghost var va_b57, va_s57 := va_lemma_Load(va_b56, va_s56, va_s51, va_op_word_reg(ESI),
            va_op_word_reg(ESP), 0);
          ghost var va_b58, va_s58 := va_lemma_POP_VOID(va_b57, va_s57, va_s51, 1 *
            ARCH_WORD_BYTES);
          ghost var va_s59, va_c59, va_b59 := va_lemma_block(va_b58, va_s58, va_s51);
          ghost var va_cond_c59, va_s60:va_state := va_lemma_ifElse(va_get_ifCond(va_c59),
            va_get_ifTrue(va_c59), va_get_ifFalse(va_c59), va_s58, va_s59);
          if (va_cond_c59)
          {
            ghost var va_b61 := va_get_block(va_get_ifTrue(va_c59));
            reveal_p__usbtd_verify_qtd32_step4_OnSuccessCheck();
            ghost var va_b63, va_s63 := va_lemma_Store(va_b61, va_s60, va_s59, va_op_word_reg(EBP),
              ARCH_WORD_BYTES, va_const_word(TRUE));
            ghost var wimpdrv_do_pbase := wimpdrv_do_get_paddr_base(va_get_globals(va_old_s),
              drv_slot);
            ghost var wimpdrv_do_pend := wimpdrv_do_get_paddr_end(va_get_globals(va_old_s),
              drv_slot);
            assert wimpdrv_do_pbase <= wimpdrv_do_pend;  // line 735 column 25 of file .\dev/usb2/usb_tds_ops/usb_tds_checks_qtd.vad
            assert p__usbtd_verify_qtd32_step3_OnSuccessCheck(va_get_globals(va_old_s), drv_slot,
              td_slot);  // line 736 column 25 of file .\dev/usb2/usb_tds_ops/usb_tds_checks_qtd.vad
            va_s59 := va_lemma_empty(va_s63, va_s59);
          }
          else
          {
            ghost var va_b68 := va_get_block(va_get_ifFalse(va_c59));
            ghost var va_b69, va_s69 := va_lemma_Store(va_b68, va_s60, va_s59, va_op_word_reg(EBP),
              ARCH_WORD_BYTES, va_const_word(FALSE));
            va_s59 := va_lemma_empty(va_s69, va_s59);
          }
          va_s51 := va_lemma_empty(va_s59, va_s51);
        }
        else
        {
          ghost var va_b70 := va_get_block(va_get_ifFalse(va_c51));
          ghost var va_b71, va_s71 := va_lemma_Store(va_b70, va_s52, va_s51, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          va_s51 := va_lemma_empty(va_s71, va_s51);
        }
        va_s39 := va_lemma_empty(va_s51, va_s39);
      }
      else
      {
        ghost var va_b72 := va_get_block(va_get_ifFalse(va_c39));
        ghost var va_b73, va_s73 := va_lemma_Store(va_b72, va_s40, va_s39, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        va_s39 := va_lemma_empty(va_s73, va_s39);
      }
      va_s30 := va_lemma_empty(va_s39, va_s30);
    }
    else
    {
      ghost var va_b74 := va_get_block(va_get_ifFalse(va_c30));
      ghost var va_b75, va_s75 := va_lemma_Store(va_b74, va_s31, va_s30, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      va_s30 := va_lemma_empty(va_s75, va_s30);
    }
    va_s21 := va_lemma_empty(va_s30, va_s21);
  }
  else
  {
    ghost var va_b76 := va_get_block(va_get_ifFalse(va_c21));
    ghost var va_b77, va_s77 := va_lemma_Store(va_b76, va_s22, va_s21, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s21 := va_lemma_empty(va_s77, va_s21);
  }
  ghost var va_b78, va_s78 := va_lemma_POP_OneReg(va_b21, va_s21, va_sM, va_op_reg_reg(EAX));
  ghost var va_b79, va_s79 := va_lemma_POP_TwoRegs(va_b78, va_s78, va_sM, va_op_reg_reg(ESI),
    va_op_reg_reg(EDI));
  ghost var va_b80, va_s80 := va_lemma_POP_OneReg(va_b79, va_s79, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s80, va_sM);
}
//--
