include "..\\..\\state_properties_OpsSaneStateSubset.i.dfy"
include "usb_pdev_utils.gen.dfy"
include "usb_tds_ops/usb_tds_ops.private.gen.dfy"
include "usb_pdev_utils.i.dfy"
//-- _usbpdev_set_slot
//--
//-- _usbpdev_clear_slot
//--
//-- _usbpdev_activate_private
//--
//-- USBPDev_ActivateIntoWimpPartition_Impl

function method{:opaque} va_code_USBPDev_ActivateIntoWimpPartition_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EDX)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EDX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_usbpdev_is_empty_addr(va_op_reg_reg(EDI), va_op_reg_reg(EDX),
    va_op_reg_reg(ESI)), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_usbpdev_find_slot_by_id(), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_usbpdevlist_find_slot_by_id(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code__usbpdev_activate_private(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), ARCH_WORD_BYTES),
    va_CCons(va_code_POP_VOID(3 * ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_op_word_reg(ESI)), va_CNil()))))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpUSBPDev_SlotID_EMPTY)), va_CNil())))), va_CNil()))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpUSBPDev_SlotID_EMPTY)), va_CNil())))), va_CNil()))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpUSBPDev_SlotID_EMPTY)), va_CNil())))),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))
}

lemma{:timeLimitMultiplier 100} va_lemma_USBPDev_ActivateIntoWimpPartition_Impl(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_USBPDev_ActivateIntoWimpPartition_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 15 *
    ARCH_WORD_BYTES + 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space)
    && (var stack_params_space := 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(va_s0.subjects, usbpdev_id) ==>
    va_s0.subjects.usbpdevs[usbpdev_id].active_in_os == false
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var new_usbpdev_addr_low := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1
    * ARCH_WORD_BYTES); var new_usbpdev_addr_high := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES); var new_usbpdev_addr_raw:uint64 :=
    UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low); var ret:uint32 :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ret == TRUE ==>
    usb_is_usbpdev_addr_valid(new_usbpdev_addr_raw) && (var new_usbpdev_addr:USBPDev_Addr :=
    usb_parse_usbpdev_addr(new_usbpdev_addr_raw); var empty_addr :=
    UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
    (usb_is_usbpdev_addr_valid(empty_addr) && new_usbpdev_addr !=
    usb_parse_usbpdev_addr(empty_addr)) && Map_USBPDevAddr_ToDevID(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, new_usbpdev_addr) in va_s0.subjects.usbpdevs)
  ensures  var new_pid := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_usbpdev_addr_low := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_usbpdev_addr_high := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var new_usbpdev_addr:uint64 :=
    UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low); var out_usbpdev_slot:word
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var ret:uint32
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); (((((((ret == TRUE ==>
    pids_is_existing_wimp_pid(va_get_globals(va_s0), new_pid)) && (ret == TRUE ==> (forall i:word
    :: usbpdev_valid_slot_id(i) ==> !(usbpdev_get_addr_low(va_get_globals(va_s0), i) ==
    new_usbpdev_addr_low && usbpdev_get_addr_high(va_get_globals(va_s0), i) ==
    new_usbpdev_addr_high)))) && (ret == TRUE ==> usb_is_usbpdev_addr_valid(new_usbpdev_addr))) &&
    (ret == TRUE ==> usbpdev_valid_slot_id(out_usbpdev_slot))) && (ret == TRUE ==>
    usbpdev_info_newvalue(va_get_globals(va_s0), va_get_globals(va_sM), out_usbpdev_slot,
    new_usbpdev_addr_low, new_usbpdev_addr_high, new_pid, WimpUSBPDev_Slot_UpdateFlag_Complete)))
    && (ret == TRUE ==> usbpdev_clear_non_mstate_relationship(va_s0, va_sM,
    usb_parse_usbpdev_addr(new_usbpdev_addr)))) && (ret != TRUE ==>
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
  reveal_va_code_USBPDev_ActivateIntoWimpPartition_Impl();
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
  ghost var va_b9, va_s9 := va_lemma_Load(va_b8, va_s8, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_usbpdev_is_empty_addr(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDI), va_op_reg_reg(EDX), va_op_reg_reg(ESI));
  ghost var va_s12, va_c12, va_b12 := va_lemma_block(va_b11, va_s11, va_sM);
  ghost var va_cond_c12, va_s13:va_state := va_lemma_ifElse(va_get_ifCond(va_c12),
    va_get_ifTrue(va_c12), va_get_ifFalse(va_c12), va_s11, va_s12);
  if (va_cond_c12)
  {
    ghost var va_b14 := va_get_block(va_get_ifTrue(va_c12));
    ghost var va_b15, va_s15 := va_lemma_Load(va_b14, va_s13, va_s12, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
    ghost var va_b16, va_s16 := va_lemma_PUSH(va_b15, va_s15, va_s12, va_op_word_reg(EDI));
    ghost var va_b17, va_s17 := va_lemma_Load(va_b16, va_s16, va_s12, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
    ghost var va_b18, va_s18 := va_lemma_PUSH(va_b17, va_s17, va_s12, va_op_word_reg(EDI));
    ghost var va_b19, va_s19 := va_lemma_usbpdev_find_slot_by_id(va_b18, va_s18, va_s12);
    ghost var va_b20, va_s20 := va_lemma_Load(va_b19, va_s19, va_s12, va_op_word_reg(ESI),
      va_op_word_reg(ESP), 0);
    ghost var va_b21, va_s21 := va_lemma_POP_VOID(va_b20, va_s20, va_s12, 2 * ARCH_WORD_BYTES);
    ghost var va_s22, va_c22, va_b22 := va_lemma_block(va_b21, va_s21, va_s12);
    ghost var va_cond_c22, va_s23:va_state := va_lemma_ifElse(va_get_ifCond(va_c22),
      va_get_ifTrue(va_c22), va_get_ifFalse(va_c22), va_s21, va_s22);
    if (va_cond_c22)
    {
      ghost var va_b24 := va_get_block(va_get_ifTrue(va_c22));
      ghost var va_b25, va_s25 := va_lemma_Load(va_b24, va_s23, va_s22, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
      ghost var va_b26, va_s26 := va_lemma_PUSH(va_b25, va_s25, va_s22, va_op_word_reg(EDI));
      ghost var va_b27, va_s27 := va_lemma_Load(va_b26, va_s26, va_s22, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
      ghost var va_b28, va_s28 := va_lemma_PUSH(va_b27, va_s27, va_s22, va_op_word_reg(EDI));
      ghost var va_b29, va_s29 := va_lemma_usbpdevlist_find_slot_by_id(va_b28, va_s28, va_s22);
      ghost var va_b30, va_s30 := va_lemma_Load(va_b29, va_s29, va_s22, va_op_word_reg(EDI),
        va_op_word_reg(ESP), 0);
      ghost var va_b31, va_s31 := va_lemma_POP_VOID(va_b30, va_s30, va_s22, 2 * ARCH_WORD_BYTES);
      ghost var va_s32, va_c32, va_b32 := va_lemma_block(va_b31, va_s31, va_s22);
      ghost var va_cond_c32, va_s33:va_state := va_lemma_ifElse(va_get_ifCond(va_c32),
        va_get_ifTrue(va_c32), va_get_ifFalse(va_c32), va_s31, va_s32);
      if (va_cond_c32)
      {
        ghost var va_b34 := va_get_block(va_get_ifTrue(va_c32));
        Lemma_usbpdevlist_clear_all_devices_ProveAllAddrsMapToExistingUSBPDevs(va_s33);
        Lemma_USBPDev_UniqueAddrLowAndHighWord_MapToUniqueUSBPDevAddr();
        ghost var va_b37, va_s37 := va_lemma_Load(va_b34, va_s33, va_s32, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
        ghost var va_b38, va_s38 := va_lemma_PUSH(va_b37, va_s37, va_s32, va_op_word_reg(EDI));
        ghost var va_b39, va_s39 := va_lemma_Load(va_b38, va_s38, va_s32, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
        ghost var va_b40, va_s40 := va_lemma_PUSH(va_b39, va_s39, va_s32, va_op_word_reg(EDI));
        ghost var va_b41, va_s41 := va_lemma_Load(va_b40, va_s40, va_s32, va_op_word_reg(EDI),
          va_op_word_reg(EBP), ARCH_WORD_BYTES);
        ghost var va_b42, va_s42 := va_lemma_PUSH(va_b41, va_s41, va_s32, va_op_word_reg(EDI));
        ghost var va_b43, va_s43 := va_lemma__usbpdev_activate_private(va_b42, va_s42, va_s32);
        ghost var va_b44, va_s44 := va_lemma_Load(va_b43, va_s43, va_s32, va_op_word_reg(EDI),
          va_op_word_reg(ESP), 0);
        ghost var va_b45, va_s45 := va_lemma_Load(va_b44, va_s44, va_s32, va_op_word_reg(ESI),
          va_op_word_reg(ESP), ARCH_WORD_BYTES);
        ghost var va_b46, va_s46 := va_lemma_POP_VOID(va_b45, va_s45, va_s32, 3 * ARCH_WORD_BYTES);
        ghost var va_b47, va_s47 := va_lemma_Store(va_b46, va_s46, va_s32, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_op_word_reg(EDI));
        ghost var va_b48, va_s48 := va_lemma_Store(va_b47, va_s47, va_s32, va_op_word_reg(EBP), 2 *
          ARCH_WORD_BYTES, va_op_word_reg(ESI));
        va_s32 := va_lemma_empty(va_s48, va_s32);
      }
      else
      {
        ghost var va_b49 := va_get_block(va_get_ifFalse(va_c32));
        ghost var va_b50, va_s50 := va_lemma_Store(va_b49, va_s33, va_s32, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        ghost var va_b51, va_s51 := va_lemma_Store(va_b50, va_s50, va_s32, va_op_word_reg(EBP), 2 *
          ARCH_WORD_BYTES, va_const_word(WimpUSBPDev_SlotID_EMPTY));
        assert va_get_globals(va_s51) == va_get_globals(va_old_s);  // line 165 column 17 of file .\dev/usb2/usb_pdev_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s51));
        va_s32 := va_lemma_empty(va_s51, va_s32);
      }
      va_s22 := va_lemma_empty(va_s32, va_s22);
    }
    else
    {
      ghost var va_b54 := va_get_block(va_get_ifFalse(va_c22));
      ghost var va_b55, va_s55 := va_lemma_Store(va_b54, va_s23, va_s22, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b56, va_s56 := va_lemma_Store(va_b55, va_s55, va_s22, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_const_word(WimpUSBPDev_SlotID_EMPTY));
      assert va_get_globals(va_s56) == va_get_globals(va_old_s);  // line 174 column 13 of file .\dev/usb2/usb_pdev_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s56));
      va_s22 := va_lemma_empty(va_s56, va_s22);
    }
    va_s12 := va_lemma_empty(va_s22, va_s12);
  }
  else
  {
    ghost var va_b59 := va_get_block(va_get_ifFalse(va_c12));
    ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s13, va_s12, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b61, va_s61 := va_lemma_Store(va_b60, va_s60, va_s12, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(WimpUSBPDev_SlotID_EMPTY));
    assert va_get_globals(va_s61) == va_get_globals(va_old_s);  // line 183 column 9 of file .\dev/usb2/usb_pdev_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s61));
    va_s12 := va_lemma_empty(va_s61, va_s12);
  }
  ghost var va_b64, va_s64 := va_lemma_POP_OneReg(va_b12, va_s12, va_sM, va_op_reg_reg(EDX));
  ghost var va_b65, va_s65 := va_lemma_POP_TwoRegs(va_b64, va_s64, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b66, va_s66 := va_lemma_POP_OneReg(va_b65, va_s65, va_sM, va_op_reg_reg(EBP));
  Lemma_modify_regs_objects_stateeq_USBPDev_ActivateIntoWimpPartitions(va_old_s, va_s66);
  va_sM := va_lemma_empty(va_s66, va_sM);
}
//--
//-- USBPDev_DeactivateFromWimpPartition_Impl

function method{:opaque} va_code_USBPDev_DeactivateFromWimpPartition_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_usbpdev_check_slot_id(va_op_reg_reg(EDI), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_usbpdev_get_update_flag(), va_CCons(va_code_Load(va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX),
    va_const_cmp(WimpUSBPDev_Slot_UpdateFlag_Complete)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_usbpdev_get_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code__usbpdev_find_referencing_secure_usbtd(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code__usbpdev_clear_slot(),
    va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(TRUE)), va_CNil()))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))
}

lemma{:timeLimitMultiplier 30} va_lemma_USBPDev_DeactivateFromWimpPartition_Impl(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_USBPDev_DeactivateFromWimpPartition_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 20 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(va_s0.subjects, usbpdev_id) ==>
    va_s0.subjects.usbpdevs[usbpdev_id].active_in_os == false
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((((((ret == TRUE ==>
    usbpdev_valid_slot_id(usbpdev_slot)) && (ret == TRUE ==>
    pids_is_existing_wimp_pid(va_get_globals(va_s0), usbpdev_get_pid(va_get_globals(va_s0),
    usbpdev_slot).v))) && (ret == TRUE ==> usbpdev_get_updateflag(va_get_globals(va_s0),
    usbpdev_slot) == WimpUSBPDev_Slot_UpdateFlag_Complete)) && (ret == TRUE ==>
    usbtds_verifiedtds_do_not_associate_usb_pdev(va_get_globals(va_s0), usbpdev_slot))) && (ret ==
    TRUE ==> usbpdev_get_pid(va_get_globals(va_sM), usbpdev_slot) == WS_PartitionID(PID_INVALID)))
    && (ret == TRUE ==> usbpdev_info_newvalue(va_get_globals(va_s0), va_get_globals(va_sM),
    usbpdev_slot, WimpUSBPDev_ADDR_EMPTY_LOW, WimpUSBPDev_ADDR_EMPTY_HIGH, PID_INVALID,
    WimpUSBPDev_Slot_UpdateFlag_Complete))) && (ret != TRUE ==>
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
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_globals(va_sM, va_update_mem(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_USBPDev_DeactivateFromWimpPartition_Impl();
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
  ghost var in_slot_id := va_get_reg(EDI, va_s9);
  ghost var va_b11, va_s11 := va_lemma_usbpdev_check_slot_id(va_b9, va_s9, va_sM,
    va_op_reg_reg(EDI), va_op_reg_reg(EAX));
  ghost var va_s12, va_c12, va_b12 := va_lemma_block(va_b11, va_s11, va_sM);
  ghost var va_cond_c12, va_s13:va_state := va_lemma_ifElse(va_get_ifCond(va_c12),
    va_get_ifTrue(va_c12), va_get_ifFalse(va_c12), va_s11, va_s12);
  if (va_cond_c12)
  {
    ghost var va_b14 := va_get_block(va_get_ifTrue(va_c12));
    ghost var va_b15, va_s15 := va_lemma_PUSH(va_b14, va_s13, va_s12, va_op_word_reg(EDI));
    ghost var va_b16, va_s16 := va_lemma_usbpdev_get_update_flag(va_b15, va_s15, va_s12);
    ghost var va_b17, va_s17 := va_lemma_Load(va_b16, va_s16, va_s12, va_op_word_reg(EAX),
      va_op_word_reg(ESP), 0);
    ghost var va_b18, va_s18 := va_lemma_POP_VOID(va_b17, va_s17, va_s12, 1 * ARCH_WORD_BYTES);
    ghost var va_s19, va_c19, va_b19 := va_lemma_block(va_b18, va_s18, va_s12);
    ghost var va_cond_c19, va_s20:va_state := va_lemma_ifElse(va_get_ifCond(va_c19),
      va_get_ifTrue(va_c19), va_get_ifFalse(va_c19), va_s18, va_s19);
    if (va_cond_c19)
    {
      ghost var va_b21 := va_get_block(va_get_ifTrue(va_c19));
      ghost var va_b22, va_s22 := va_lemma_PUSH(va_b21, va_s20, va_s19, va_op_word_reg(EDI));
      ghost var va_b23, va_s23 := va_lemma_usbpdev_get_pid(va_b22, va_s22, va_s19);
      ghost var va_b24, va_s24 := va_lemma_Load(va_b23, va_s23, va_s19, va_op_word_reg(EDX),
        va_op_word_reg(ESP), 0);
      ghost var va_b25, va_s25 := va_lemma_POP_VOID(va_b24, va_s24, va_s19, 1 * ARCH_WORD_BYTES);
      ghost var va_b26, va_s26 := va_lemma_PUSH_VOID(va_b25, va_s25, va_s19, 1 * ARCH_WORD_BYTES);
      ghost var va_b27, va_s27 := va_lemma_PUSH(va_b26, va_s26, va_s19, va_op_word_reg(EDX));
      ghost var va_b28, va_s28 := va_lemma_pids_is_existing_wimp_pid(va_b27, va_s27, va_s19);
      ghost var va_b29, va_s29 := va_lemma_Load(va_b28, va_s28, va_s19, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b30, va_s30 := va_lemma_POP_VOID(va_b29, va_s29, va_s19, 2 * ARCH_WORD_BYTES);
      ghost var va_s31, va_c31, va_b31 := va_lemma_block(va_b30, va_s30, va_s19);
      ghost var va_cond_c31, va_s32:va_state := va_lemma_ifElse(va_get_ifCond(va_c31),
        va_get_ifTrue(va_c31), va_get_ifFalse(va_c31), va_s30, va_s31);
      if (va_cond_c31)
      {
        ghost var va_b33 := va_get_block(va_get_ifTrue(va_c31));
        ghost var va_b34, va_s34 := va_lemma_PUSH_VOID(va_b33, va_s32, va_s31, 1 * ARCH_WORD_BYTES);
        ghost var va_b35, va_s35 := va_lemma_PUSH(va_b34, va_s34, va_s31, va_op_word_reg(EDI));
        ghost var va_b36, va_s36 := va_lemma__usbpdev_find_referencing_secure_usbtd(va_b35, va_s35,
          va_s31);
        ghost var va_b37, va_s37 := va_lemma_Load(va_b36, va_s36, va_s31, va_op_word_reg(EAX),
          va_op_word_reg(ESP), 0);
        ghost var va_b38, va_s38 := va_lemma_POP_VOID(va_b37, va_s37, va_s31, 2 * ARCH_WORD_BYTES);
        ghost var va_s39, va_c39, va_b39 := va_lemma_block(va_b38, va_s38, va_s31);
        ghost var va_cond_c39, va_s40:va_state := va_lemma_ifElse(va_get_ifCond(va_c39),
          va_get_ifTrue(va_c39), va_get_ifFalse(va_c39), va_s38, va_s39);
        if (va_cond_c39)
        {
          ghost var va_b41 := va_get_block(va_get_ifTrue(va_c39));
          assert usbtds_verifiedtds_do_not_associate_usb_pdev(va_get_globals(va_old_s),
            in_slot_id);  // line 299 column 21 of file .\dev/usb2/usb_pdev_ops_impl.vad
          ghost var va_b43, va_s43 := va_lemma_PUSH(va_b41, va_s40, va_s39, va_op_word_reg(EDI));
          ghost var va_b44, va_s44 := va_lemma__usbpdev_clear_slot(va_b43, va_s43, va_s39);
          ghost var va_b45, va_s45 := va_lemma_POP_VOID(va_b44, va_s44, va_s39, 1 *
            ARCH_WORD_BYTES);
          ghost var va_b46, va_s46 := va_lemma_Store(va_b45, va_s45, va_s39, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          va_s39 := va_lemma_empty(va_s46, va_s39);
        }
        else
        {
          ghost var va_b47 := va_get_block(va_get_ifFalse(va_c39));
          ghost var va_b48, va_s48 := va_lemma_Store(va_b47, va_s40, va_s39, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s48) == va_get_globals(va_old_s);  // line 313 column 21 of file .\dev/usb2/usb_pdev_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s48));
          va_s39 := va_lemma_empty(va_s48, va_s39);
        }
        va_s31 := va_lemma_empty(va_s39, va_s31);
      }
      else
      {
        ghost var va_b51 := va_get_block(va_get_ifFalse(va_c31));
        ghost var va_b52, va_s52 := va_lemma_Store(va_b51, va_s32, va_s31, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s52) == va_get_globals(va_old_s);  // line 321 column 17 of file .\dev/usb2/usb_pdev_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s52));
        va_s31 := va_lemma_empty(va_s52, va_s31);
      }
      va_s19 := va_lemma_empty(va_s31, va_s19);
    }
    else
    {
      ghost var va_b55 := va_get_block(va_get_ifFalse(va_c19));
      ghost var va_b56, va_s56 := va_lemma_Store(va_b55, va_s20, va_s19, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s56) == va_get_globals(va_old_s);  // line 329 column 13 of file .\dev/usb2/usb_pdev_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s56));
      va_s19 := va_lemma_empty(va_s56, va_s19);
    }
    va_s12 := va_lemma_empty(va_s19, va_s12);
  }
  else
  {
    ghost var va_b59 := va_get_block(va_get_ifFalse(va_c12));
    ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s13, va_s12, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s60) == va_get_globals(va_old_s);  // line 337 column 9 of file .\dev/usb2/usb_pdev_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s60));
    va_s12 := va_lemma_empty(va_s60, va_s12);
  }
  ghost var va_b63, va_s63 := va_lemma_POP_Reg1ToReg6(va_b12, va_s12, va_sM);
  ghost var va_b64, va_s64 := va_lemma_POP_OneReg(va_b63, va_s63, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s64, va_sM);
}
//--
//-- USBPDev_ActivateIntoWimpPartition_Inner

function method{:opaque} va_code_USBPDev_ActivateIntoWimpPartition_Inner():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EDX)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_usbpdevlist_find_slot_by_id(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDI), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code__usbpdev_activate_private(),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP), 0),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), ARCH_WORD_BYTES),
    va_CCons(va_code_POP_VOID(3 * ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_op_word_reg(ESI)), va_CNil()))))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpUSBPDev_SlotID_EMPTY)), va_CNil())))),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))
}

lemma{:timeLimitMultiplier 10} va_lemma_USBPDev_ActivateIntoWimpPartition_Inner(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_USBPDev_ActivateIntoWimpPartition_Inner(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 15 *
    ARCH_WORD_BYTES + 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space)
    && (var stack_params_space := 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(va_s0.subjects, usbpdev_id) ==>
    va_s0.subjects.usbpdevs[usbpdev_id].active_in_os == false
  requires var new_usbpdev_addr_low := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1
    * ARCH_WORD_BYTES); var new_usbpdev_addr_high := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES); var new_usbpdev_addr_raw:uint64 :=
    UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low); var ret:uint32 :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usb_is_usbpdev_addr_valid(new_usbpdev_addr_raw) && (var new_usbpdev_addr:USBPDev_Addr :=
    usb_parse_usbpdev_addr(new_usbpdev_addr_raw); var empty_addr :=
    UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
    (usb_is_usbpdev_addr_valid(empty_addr) && new_usbpdev_addr !=
    usb_parse_usbpdev_addr(empty_addr)) && Map_USBPDevAddr_ToDevID(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, new_usbpdev_addr) in va_s0.subjects.usbpdevs)
  requires var new_pid := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_usbpdev_addr_low := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_usbpdev_addr_high := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var new_usbpdev_addr_raw:uint64 :=
    UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
    (pids_is_existing_wimp_pid(va_get_globals(va_s0), new_pid) && (forall i:word ::
    usbpdev_valid_slot_id(i) ==> !(usbpdev_get_addr_low(va_get_globals(va_s0), i) ==
    new_usbpdev_addr_low && usbpdev_get_addr_high(va_get_globals(va_s0), i) ==
    new_usbpdev_addr_high))) && usb_is_usbpdev_addr_valid(new_usbpdev_addr_raw)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var new_pid := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_usbpdev_addr_low := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_usbpdev_addr_high := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var new_usbpdev_addr:uint64 :=
    UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low); var out_usbpdev_slot:word
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var ret:uint32
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((((ret == TRUE ==>
    usbpdev_valid_slot_id(out_usbpdev_slot)) && (ret == TRUE ==>
    usbpdev_info_newvalue(va_get_globals(va_s0), va_get_globals(va_sM), out_usbpdev_slot,
    new_usbpdev_addr_low, new_usbpdev_addr_high, new_pid, WimpUSBPDev_Slot_UpdateFlag_Complete)))
    && (ret == TRUE ==> usbpdev_clear_non_mstate_relationship(va_s0, va_sM,
    usb_parse_usbpdev_addr(new_usbpdev_addr)))) && (ret != TRUE ==>
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
  reveal_va_code_USBPDev_ActivateIntoWimpPartition_Inner();
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
  ghost var va_b9, va_s9 := va_lemma_Load(va_b8, va_s8, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var va_b10, va_s10 := va_lemma_PUSH(va_b9, va_s9, va_sM, va_op_word_reg(EDI));
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_PUSH(va_b11, va_s11, va_sM, va_op_word_reg(EDI));
  ghost var va_b13, va_s13 := va_lemma_usbpdevlist_find_slot_by_id(va_b12, va_s12, va_sM);
  ghost var va_b14, va_s14 := va_lemma_Load(va_b13, va_s13, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(ESP), 0);
  ghost var va_b15, va_s15 := va_lemma_POP_VOID(va_b14, va_s14, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s16, va_c16, va_b16 := va_lemma_block(va_b15, va_s15, va_sM);
  ghost var va_cond_c16, va_s17:va_state := va_lemma_ifElse(va_get_ifCond(va_c16),
    va_get_ifTrue(va_c16), va_get_ifFalse(va_c16), va_s15, va_s16);
  if (va_cond_c16)
  {
    ghost var va_b18 := va_get_block(va_get_ifTrue(va_c16));
    Lemma_usbpdevlist_clear_all_devices_ProveAllAddrsMapToExistingUSBPDevs(va_s17);
    Lemma_USBPDev_UniqueAddrLowAndHighWord_MapToUniqueUSBPDevAddr();
    ghost var va_b21, va_s21 := va_lemma_Load(va_b18, va_s17, va_s16, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
    ghost var va_b22, va_s22 := va_lemma_PUSH(va_b21, va_s21, va_s16, va_op_word_reg(EDI));
    ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s16, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
    ghost var va_b24, va_s24 := va_lemma_PUSH(va_b23, va_s23, va_s16, va_op_word_reg(EDI));
    ghost var va_b25, va_s25 := va_lemma_Load(va_b24, va_s24, va_s16, va_op_word_reg(EDI),
      va_op_word_reg(EBP), ARCH_WORD_BYTES);
    ghost var va_b26, va_s26 := va_lemma_PUSH(va_b25, va_s25, va_s16, va_op_word_reg(EDI));
    ghost var va_b27, va_s27 := va_lemma__usbpdev_activate_private(va_b26, va_s26, va_s16);
    ghost var va_b28, va_s28 := va_lemma_Load(va_b27, va_s27, va_s16, va_op_word_reg(EDI),
      va_op_word_reg(ESP), 0);
    ghost var va_b29, va_s29 := va_lemma_Load(va_b28, va_s28, va_s16, va_op_word_reg(ESI),
      va_op_word_reg(ESP), ARCH_WORD_BYTES);
    ghost var va_b30, va_s30 := va_lemma_POP_VOID(va_b29, va_s29, va_s16, 3 * ARCH_WORD_BYTES);
    ghost var va_b31, va_s31 := va_lemma_Store(va_b30, va_s30, va_s16, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_op_word_reg(EDI));
    ghost var va_b32, va_s32 := va_lemma_Store(va_b31, va_s31, va_s16, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_op_word_reg(ESI));
    va_s16 := va_lemma_empty(va_s32, va_s16);
  }
  else
  {
    ghost var va_b33 := va_get_block(va_get_ifFalse(va_c16));
    ghost var va_b34, va_s34 := va_lemma_Store(va_b33, va_s17, va_s16, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b35, va_s35 := va_lemma_Store(va_b34, va_s34, va_s16, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(WimpUSBPDev_SlotID_EMPTY));
    assert va_get_globals(va_s35) == va_get_globals(va_old_s);  // line 484 column 9 of file .\dev/usb2/usb_pdev_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s35));
    va_s16 := va_lemma_empty(va_s35, va_s16);
  }
  ghost var va_b38, va_s38 := va_lemma_POP_OneReg(va_b16, va_s16, va_sM, va_op_reg_reg(EDX));
  ghost var va_b39, va_s39 := va_lemma_POP_TwoRegs(va_b38, va_s38, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b40, va_s40 := va_lemma_POP_OneReg(va_b39, va_s39, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s40, va_sM);
}
//--
//-- _usbpdev_activate_private

function method{:opaque} va_code__usbpdev_activate_private():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(ESI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_const_word(WimpUSBPDev_ADDR_EMPTY_HIGH)),
    va_CCons(va_code_PUSH(va_const_word(WimpUSBPDev_ADDR_EMPTY_LOW)),
    va_CCons(va_code_usbpdev_find_slot_by_id(), va_CCons(va_code_Load(va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(ESP),
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_usbpdev_check_dev_addr(va_op_reg_reg(ECX), va_op_reg_reg(EBX),
    va_op_reg_reg(EAX)), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_PUSH(va_op_word_reg(ESI)),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code__usbpdev_set_slot(),
    va_CCons(va_code_POP_VOID(4 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_Reg1ToReg6(),
    va_CCons(va_code_PUSH(va_op_word_reg(ECX)), va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_CALL_USBPDev_Clear(), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_POP_Reg1ToReg6(), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EDI)), va_CNil()))))))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpUSBPDev_SlotID_EMPTY)), va_CNil())))), va_CNil()))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpUSBPDev_SlotID_EMPTY)), va_CNil())))), va_CNil())))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpUSBPDev_SlotID_EMPTY)), va_CNil())))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))
}

lemma{:timeLimitMultiplier 50} va_lemma__usbpdev_activate_private(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbpdev_activate_private(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 6 *
    ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space)
    && (var stack_params_space := 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires var new_usbpdev_addr_low := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1
    * ARCH_WORD_BYTES); var new_usbpdev_addr_high := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES); var new_usbpdev_addr_raw:uint64 :=
    UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low);
    usb_is_usbpdev_addr_valid(new_usbpdev_addr_raw) && (var new_usbpdev_addr:USBPDev_Addr :=
    usb_parse_usbpdev_addr(new_usbpdev_addr_raw); var empty_addr :=
    UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
    (usb_is_usbpdev_addr_valid(empty_addr) && new_usbpdev_addr !=
    usb_parse_usbpdev_addr(empty_addr)) && Map_USBPDevAddr_ToDevID(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, new_usbpdev_addr) in va_s0.subjects.usbpdevs)
  requires var new_usbpdev_addr_low := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1
    * ARCH_WORD_BYTES); var new_usbpdev_addr_high := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 2 * ARCH_WORD_BYTES); var new_usbpdev_addr_raw:uint64 :=
    UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low); var
    new_usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw); new_usbpdev_addr
    in usbpdevlist_get_all_non_empty_addrs(va_get_globals(va_s0))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_addr_low:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_addr_high:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); forall i:uint32 :: (usbpdev_valid_slot_id(i) &&
    usbpdev_get_updateflag(va_get_globals(va_s0), i) == WimpUSBPDev_Slot_UpdateFlag_Complete) &&
    !(usbpdev_get_addr_low(va_get_globals(va_s0), i) == WimpUSBPDev_ADDR_EMPTY_LOW &&
    usbpdev_get_addr_high(va_get_globals(va_s0), i) == WimpUSBPDev_ADDR_EMPTY_HIGH) ==>
    usbpdev_get_addr_low(va_get_globals(va_s0), i) != new_addr_low ||
    usbpdev_get_addr_high(va_get_globals(va_s0), i) != new_addr_high
  requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(va_s0.subjects, usbpdev_id) ==>
    va_s0.subjects.usbpdevs[usbpdev_id].active_in_os == false
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var new_pid := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_usbpdev_addr_low := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_usbpdev_addr_high := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var new_usbpdev_addr:uint64 :=
    UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low); var out_usbpdev_slot:word
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var ret:uint32
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((((((ret == TRUE ==>
    pids_is_existing_wimp_pid(va_get_globals(va_s0), new_pid)) && (ret == TRUE ==>
    usb_is_usbpdev_addr_valid(new_usbpdev_addr))) && (ret == TRUE ==>
    usbpdev_valid_slot_id(out_usbpdev_slot))) && (ret == TRUE ==>
    usbpdev_info_newvalue(va_get_globals(va_s0), va_get_globals(va_sM), out_usbpdev_slot,
    new_usbpdev_addr_low, new_usbpdev_addr_high, new_pid, WimpUSBPDev_Slot_UpdateFlag_Complete)))
    && (ret == TRUE ==> usbpdev_clear_non_mstate_relationship(va_s0, va_sM,
    usb_parse_usbpdev_addr(new_usbpdev_addr)))) && (ret != TRUE ==>
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
  reveal_va_code__usbpdev_activate_private();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_PUSH_VOID(va_b10, va_s10, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_PUSH(va_b12, va_s12, va_sM, va_op_word_reg(ESI));
  ghost var va_b14, va_s14 := va_lemma_pids_is_existing_wimp_pid(va_b13, va_s13, va_sM);
  ghost var va_b15, va_s15 := va_lemma_Load(va_b14, va_s14, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0);
  ghost var va_b16, va_s16 := va_lemma_POP_VOID(va_b15, va_s15, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s17, va_c17, va_b17 := va_lemma_block(va_b16, va_s16, va_sM);
  ghost var va_cond_c17, va_s18:va_state := va_lemma_ifElse(va_get_ifCond(va_c17),
    va_get_ifTrue(va_c17), va_get_ifFalse(va_c17), va_s16, va_s17);
  if (va_cond_c17)
  {
    ghost var va_b19 := va_get_block(va_get_ifTrue(va_c17));
    ghost var va_b20, va_s20 := va_lemma_PUSH(va_b19, va_s18, va_s17,
      va_const_word(WimpUSBPDev_ADDR_EMPTY_HIGH));
    ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s20, va_s17,
      va_const_word(WimpUSBPDev_ADDR_EMPTY_LOW));
    ghost var va_b22, va_s22 := va_lemma_usbpdev_find_slot_by_id(va_b21, va_s21, va_s17);
    ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s17, va_op_word_reg(EAX),
      va_op_word_reg(ESP), 0);
    ghost var va_b24, va_s24 := va_lemma_Load(va_b23, va_s23, va_s17, va_op_word_reg(EDI),
      va_op_word_reg(ESP), ARCH_WORD_BYTES);
    ghost var va_b25, va_s25 := va_lemma_POP_VOID(va_b24, va_s24, va_s17, 2 * ARCH_WORD_BYTES);
    ghost var va_s26, va_c26, va_b26 := va_lemma_block(va_b25, va_s25, va_s17);
    ghost var va_cond_c26, va_s27:va_state := va_lemma_ifElse(va_get_ifCond(va_c26),
      va_get_ifTrue(va_c26), va_get_ifFalse(va_c26), va_s25, va_s26);
    if (va_cond_c26)
    {
      ghost var va_b28 := va_get_block(va_get_ifTrue(va_c26));
      Lemma__usbpdev_find_slot_Prove_usbtds_verifiedtds_do_not_associate_usb_pdev(va_get_globals(va_s27),
        va_get_reg(EDI, va_s27));
      assert usbtds_verifiedtds_do_not_associate_usb_pdev(va_get_globals(va_s27), va_get_reg(EDI,
        va_s27));  // line 618 column 13 of file .\dev/usb2/usb_pdev_ops_impl.vad
      ghost var va_b31, va_s31 := va_lemma_Load(va_b28, va_s27, va_s26, va_op_word_reg(ECX),
        va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
      ghost var va_b32, va_s32 := va_lemma_Load(va_b31, va_s31, va_s26, va_op_word_reg(EBX),
        va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
      ghost var new_usbpdev_addr:uint64 := UInt64_FromTwoUInt32s(va_get_reg(ECX, va_s32),
        va_get_reg(EBX, va_s32));
      ghost var va_b34, va_s34 := va_lemma_usbpdev_check_dev_addr(va_b32, va_s32, va_s26,
        va_op_reg_reg(ECX), va_op_reg_reg(EBX), va_op_reg_reg(EAX));
      ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b34, va_s34, va_s26);
      ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
        va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s34, va_s35);
      if (va_cond_c35)
      {
        ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
        assert usb_is_usbpdev_addr_valid(new_usbpdev_addr);  // line 628 column 17 of file .\dev/usb2/usb_pdev_ops_impl.vad
        ghost var va_b39, va_s39 := va_lemma_PUSH(va_b37, va_s36, va_s35, va_op_word_reg(ECX));
        ghost var va_b40, va_s40 := va_lemma_PUSH(va_b39, va_s39, va_s35, va_op_word_reg(EBX));
        ghost var va_b41, va_s41 := va_lemma_PUSH(va_b40, va_s40, va_s35, va_op_word_reg(ESI));
        ghost var va_b42, va_s42 := va_lemma_PUSH(va_b41, va_s41, va_s35, va_op_word_reg(EDI));
        ghost var va_b43, va_s43 := va_lemma__usbpdev_set_slot(va_b42, va_s42, va_s35);
        ghost var va_b44, va_s44 := va_lemma_POP_VOID(va_b43, va_s43, va_s35, 4 * ARCH_WORD_BYTES);
        ghost var va_b45, va_s45 := va_lemma_PUSH_Reg1ToReg6(va_b44, va_s44, va_s35);
        ghost var va_b46, va_s46 := va_lemma_PUSH(va_b45, va_s45, va_s35, va_op_word_reg(ECX));
        ghost var va_b47, va_s47 := va_lemma_PUSH(va_b46, va_s46, va_s35, va_op_word_reg(EBX));
        ghost var va_b48, va_s48 := va_lemma_CALL_USBPDev_Clear(va_b47, va_s47, va_s35);
        ghost var va_b49, va_s49 := va_lemma_POP_VOID(va_b48, va_s48, va_s35, 2 * ARCH_WORD_BYTES);
        ghost var va_b50, va_s50 := va_lemma_POP_Reg1ToReg6(va_b49, va_s49, va_s35);
        ghost var va_b51, va_s51 := va_lemma_Store(va_b50, va_s50, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(TRUE));
        ghost var va_b52, va_s52 := va_lemma_Store(va_b51, va_s51, va_s35, va_op_word_reg(EBP), 2 *
          ARCH_WORD_BYTES, va_op_word_reg(EDI));
        va_s35 := va_lemma_empty(va_s52, va_s35);
      }
      else
      {
        ghost var va_b53 := va_get_block(va_get_ifFalse(va_c35));
        ghost var va_b54, va_s54 := va_lemma_Store(va_b53, va_s36, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        ghost var va_b55, va_s55 := va_lemma_Store(va_b54, va_s54, va_s35, va_op_word_reg(EBP), 2 *
          ARCH_WORD_BYTES, va_const_word(WimpUSBPDev_SlotID_EMPTY));
        assert va_get_globals(va_s55) == va_get_globals(va_old_s);  // line 655 column 17 of file .\dev/usb2/usb_pdev_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s55));
        va_s35 := va_lemma_empty(va_s55, va_s35);
      }
      va_s26 := va_lemma_empty(va_s35, va_s26);
    }
    else
    {
      ghost var va_b58 := va_get_block(va_get_ifFalse(va_c26));
      ghost var va_b59, va_s59 := va_lemma_Store(va_b58, va_s27, va_s26, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s59, va_s26, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_const_word(WimpUSBPDev_SlotID_EMPTY));
      assert va_get_globals(va_s60) == va_get_globals(va_old_s);  // line 664 column 13 of file .\dev/usb2/usb_pdev_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s60));
      va_s26 := va_lemma_empty(va_s60, va_s26);
    }
    va_s17 := va_lemma_empty(va_s26, va_s17);
  }
  else
  {
    ghost var va_b63 := va_get_block(va_get_ifFalse(va_c17));
    ghost var va_b64, va_s64 := va_lemma_Store(va_b63, va_s18, va_s17, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b65, va_s65 := va_lemma_Store(va_b64, va_s64, va_s17, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(WimpUSBPDev_SlotID_EMPTY));
    assert va_get_globals(va_s65) == va_get_globals(va_old_s);  // line 673 column 9 of file .\dev/usb2/usb_pdev_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s65));
    va_s17 := va_lemma_empty(va_s65, va_s17);
  }
  ghost var va_b68, va_s68 := va_lemma_POP_Reg1ToReg6(va_b17, va_s17, va_sM);
  ghost var va_b69, va_s69 := va_lemma_POP_OneReg(va_b68, va_s68, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s69, va_sM);
}
//--
//-- _usbpdev_clear_slot

function method{:opaque} va_code__usbpdev_clear_slot():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES), va_CCons(va_code_PUSH_IMM(PID_INVALID),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_usbpdev_set_pid_to_invalid(),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_IMM(WimpUSBPDev_ADDR_EMPTY_HIGH),
    va_CCons(va_code_PUSH_IMM(WimpUSBPDev_ADDR_EMPTY_LOW),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_usbpdev_set_addr(),
    va_CCons(va_code_POP_VOID(3 * ARCH_WORD_BYTES),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))
}

lemma va_lemma__usbpdev_clear_slot(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbpdev_clear_slot(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 2 * ARCH_WORD_BYTES + 9 * ARCH_WORD_BYTES + 3 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbpdev_valid_slot_id(slot) && (forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(va_s0.subjects,
    usbpdev_id) ==> va_s0.subjects.usbpdevs[usbpdev_id].active_in_os == false)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtds_verifiedtds_do_not_associate_usb_pdev(va_get_globals(va_s0), slot)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbpdev_info_newvalue(va_get_globals(va_s0), va_get_globals(va_sM), usbpdev_slot,
    WimpUSBPDev_ADDR_EMPTY_LOW, WimpUSBPDev_ADDR_EMPTY_HIGH, PID_INVALID,
    WimpUSBPDev_Slot_UpdateFlag_Complete)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code__usbpdev_clear_slot();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_p_wimpdrv_slot_equal();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b6, va_s6 := va_lemma_PUSH_OneReg(va_b4, va_s4, va_sM, va_op_reg_reg(EDI));
  ghost var va_b7, va_s7 := va_lemma_Load(va_b6, va_s6, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var in_slot_id := va_get_reg(EDI, va_s7);
  ghost var new_id:uint64 := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH,
    WimpUSBPDev_ADDR_EMPTY_LOW);
  Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty();
  assert usb_is_usbpdev_addr_valid(new_id);  // line 749 column 5 of file .\dev/usb2/usb_pdev_ops_impl.vad
  ghost var va_b12, va_s12 := va_lemma_PUSH_IMM(va_b7, va_s7, va_sM, PID_INVALID);
  ghost var va_b13, va_s13 := va_lemma_PUSH(va_b12, va_s12, va_sM, va_op_word_reg(EDI));
  ghost var va_b14, va_s14 := va_lemma_usbpdev_set_pid_to_invalid(va_b13, va_s13, va_sM);
  ghost var va_b15, va_s15 := va_lemma_POP_VOID(va_b14, va_s14, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var globals1 := va_get_globals(va_s15);
  ghost var vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + in_slot_id * WimpUSBPDev_Info_ENTRY_SZ
    + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
  assert globals1 == global_write_word(va_get_globals(va_old_s), G_WimpUSBPDev_Info(), vaddr,
    PID_INVALID);  // line 759 column 5 of file .\dev/usb2/usb_pdev_ops_impl.vad
  Lemma_usbtds_verifiedtds_do_not_associate_usb_pdev_HoldIfGUSBTDMemUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_s15), in_slot_id);
  assert usbtds_verifiedtds_do_not_associate_usb_pdev(va_get_globals(va_s15), in_slot_id);  // line 762 column 5 of file .\dev/usb2/usb_pdev_ops_impl.vad
  ghost var va_b21, va_s21 := va_lemma_PUSH_IMM(va_b15, va_s15, va_sM, WimpUSBPDev_ADDR_EMPTY_HIGH);
  ghost var va_b22, va_s22 := va_lemma_PUSH_IMM(va_b21, va_s21, va_sM, WimpUSBPDev_ADDR_EMPTY_LOW);
  ghost var va_b23, va_s23 := va_lemma_PUSH(va_b22, va_s22, va_sM, va_op_word_reg(EDI));
  ghost var va_b24, va_s24 := va_lemma_usbpdev_set_addr(va_b23, va_s23, va_sM);
  ghost var va_b25, va_s25 := va_lemma_POP_VOID(va_b24, va_s24, va_sM, 3 * ARCH_WORD_BYTES);
  assert usbpdev_info_newvalue(globals1, va_get_globals(va_s25), in_slot_id,
    WimpUSBPDev_ADDR_EMPTY_LOW, WimpUSBPDev_ADDR_EMPTY_HIGH, PID_INVALID,
    WimpUSBPDev_Slot_UpdateFlag_Complete);  // line 770 column 5 of file .\dev/usb2/usb_pdev_ops_impl.vad
  Lemma__usbpdev_clear_slot_ProveProperty1(va_get_globals(va_old_s), globals1,
    va_get_globals(va_s25), in_slot_id);
  ghost var va_b28, va_s28 := va_lemma_POP_OneReg(va_b25, va_s25, va_sM, va_op_reg_reg(EDI));
  ghost var va_b29, va_s29 := va_lemma_POP_OneReg(va_b28, va_s28, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s29, va_sM);
}
//--
//-- _usbpdev_set_slot

function method{:opaque} va_code__usbpdev_set_slot():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(ESI)), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(ESI)),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_usbpdev_set_addr(),
    va_CCons(va_code_POP_VOID(3 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(ESI)),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_usbpdev_set_pid_to_valid(),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))))
}

lemma{:timeLimitMultiplier 10} va_lemma__usbpdev_set_slot(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbpdev_set_slot(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 3 * ARCH_WORD_BYTES + 9 * ARCH_WORD_BYTES + 3 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 4 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbpdev_valid_slot_id(slot)
  requires var new_usbpdev_addr_low:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)
    + 2 * ARCH_WORD_BYTES); var new_usbpdev_addr_high:word := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES); var new_usbpdev_addr_raw:uint64 :=
    UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low); !(new_usbpdev_addr_low ==
    WimpUSBPDev_ADDR_EMPTY_LOW && new_usbpdev_addr_high == WimpUSBPDev_ADDR_EMPTY_HIGH) &&
    usb_is_usbpdev_addr_valid(new_usbpdev_addr_raw)
  requires var new_usbpdev_addr_low:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)
    + 2 * ARCH_WORD_BYTES); var new_usbpdev_addr_high:word := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES); var new_usbpdev_addr_raw:uint64 :=
    UInt64_FromTwoUInt32s(new_usbpdev_addr_high, new_usbpdev_addr_low); var
    new_usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(new_usbpdev_addr_raw); new_usbpdev_addr
    in usbpdevlist_get_all_non_empty_addrs(va_get_globals(va_s0))
  requires var new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); WS_PartitionID(new_pid) in pids_parse_g_wimp_pids(va_get_globals(va_s0)) &&
    (forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(va_s0.subjects, usbpdev_id) ==>
    va_s0.subjects.usbpdevs[usbpdev_id].active_in_os == false)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtds_verifiedtds_do_not_associate_usb_pdev(va_get_globals(va_s0), slot)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_addr_low:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); var new_addr_high:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); forall i:uint32 :: ((usbpdev_valid_slot_id(i) && i != slot) &&
    usbpdev_get_updateflag(va_get_globals(va_s0), i) == WimpUSBPDev_Slot_UpdateFlag_Complete) &&
    !(usbpdev_get_addr_low(va_get_globals(va_s0), i) == WimpUSBPDev_ADDR_EMPTY_LOW &&
    usbpdev_get_addr_high(va_get_globals(va_s0), i) == WimpUSBPDev_ADDR_EMPTY_HIGH) ==>
    usbpdev_get_addr_low(va_get_globals(va_s0), i) != new_addr_low ||
    usbpdev_get_addr_high(va_get_globals(va_s0), i) != new_addr_high
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var
    new_usbpdev_addr_low:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); var new_usbpdev_addr_high:word := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES); usbpdev_info_newvalue(va_get_globals(va_s0),
    va_get_globals(va_sM), usbpdev_slot, new_usbpdev_addr_low, new_usbpdev_addr_high, new_pid,
    WimpUSBPDev_Slot_UpdateFlag_Complete)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code__usbpdev_set_slot();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_p_wimpdrv_slot_equal();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b4, va_s4, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b8, va_s8 := va_lemma_Load(va_b7, va_s7, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var in_slot_id := va_get_reg(EDI, va_s8);
  ghost var va_b10, va_s10 := va_lemma_Load(va_b8, va_s8, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_PUSH(va_b10, va_s10, va_sM, va_op_word_reg(ESI));
  ghost var new_usbpdev_addr_high := va_get_reg(ESI, va_s11);
  ghost var va_b13, va_s13 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var va_b14, va_s14 := va_lemma_PUSH(va_b13, va_s13, va_sM, va_op_word_reg(ESI));
  ghost var new_usbpdev_addr_low := va_get_reg(ESI, va_s14);
  ghost var va_b16, va_s16 := va_lemma_PUSH(va_b14, va_s14, va_sM, va_op_word_reg(EDI));
  ghost var va_b17, va_s17 := va_lemma_usbpdev_set_addr(va_b16, va_s16, va_sM);
  ghost var va_b18, va_s18 := va_lemma_POP_VOID(va_b17, va_s17, va_sM, 3 * ARCH_WORD_BYTES);
  ghost var globals1 := va_get_globals(va_s18);
  assert usbpdev_info_newvalue(va_get_globals(va_old_s), globals1, va_get_reg(EDI, va_s18),
    new_usbpdev_addr_low, new_usbpdev_addr_high, usbpdev_get_pid(va_get_globals(va_old_s),
    va_get_reg(EDI, va_s18)).v, WimpUSBPDev_Slot_UpdateFlag_Complete);  // line 892 column 5 of file .\dev/usb2/usb_pdev_ops_impl.vad
  ghost var va_b21, va_s21 := va_lemma_Load(va_b18, va_s18, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b22, va_s22 := va_lemma_PUSH(va_b21, va_s21, va_sM, va_op_word_reg(ESI));
  ghost var new_pid := va_get_reg(ESI, va_s22);
  ghost var va_b24, va_s24 := va_lemma_PUSH(va_b22, va_s22, va_sM, va_op_word_reg(EDI));
  ghost var va_b25, va_s25 := va_lemma_usbpdev_set_pid_to_valid(va_b24, va_s24, va_sM);
  ghost var va_b26, va_s26 := va_lemma_POP_VOID(va_b25, va_s25, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + in_slot_id * WimpUSBPDev_Info_ENTRY_SZ
    + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
  assert va_get_globals(va_s26) == global_write_word(globals1, G_WimpUSBPDev_Info(), vaddr,
    new_pid);  // line 903 column 5 of file .\dev/usb2/usb_pdev_ops_impl.vad
  Lemma__usbpdev_set_slot_ProveProperty1(va_get_globals(va_old_s), globals1,
    va_get_globals(va_s26), in_slot_id, new_usbpdev_addr_low, new_usbpdev_addr_high, new_pid);
  ghost var va_b30, va_s30 := va_lemma_POP_TwoRegs(va_b26, va_s26, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b31, va_s31 := va_lemma_POP_OneReg(va_b30, va_s30, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s31, va_sM);
}
//--
// Prove the property 1 of <_usbpdev_clear_slot>
// [TODO][Need fix] The proof code does not quite make sense. We leave it here as the proof goes through
lemma Lemma__usbpdev_clear_slot_ProveProperty1(
    old_globals:globalsmap, globals1:globalsmap, new_globals:globalsmap, slot:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbpdev_valid_slot_id(slot)

    requires var vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
            is_gvar_valid_addr(G_WimpUSBPDev_Info(), vaddr)

    requires var vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
            globals1 == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr, PID_INVALID)

    requires usbpdev_info_newvalue(globals1, new_globals, slot, WimpUSBPDev_ADDR_EMPTY_LOW, WimpUSBPDev_ADDR_EMPTY_HIGH, PID_INVALID, WimpUSBPDev_Slot_UpdateFlag_Complete);

    ensures usbpdev_info_newvalue(old_globals, new_globals, slot, WimpUSBPDev_ADDR_EMPTY_LOW, WimpUSBPDev_ADDR_EMPTY_HIGH, PID_INVALID, WimpUSBPDev_Slot_UpdateFlag_Complete)
{
    reveal p_usbpdev_slot_equal();

    // Prove other global variables are unchanged
    forall i:uint32 | usbpdev_valid_slot_id(i) && i != slot
        ensures p_usbpdev_slot_equal(old_globals, new_globals, i)
    {
        // Dafny can automatically prove it
    }
    assert globals_other_gvar_unchanged(old_globals, new_globals, G_WimpUSBPDev_Info());

    // Apply usbpdev_info_newvalue 
    var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset;
    var vaddr2 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset;
    var vaddr3 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
    var vaddr4 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;

    var t_globals1 := global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, WimpUSBPDev_ADDR_EMPTY_LOW);
    var t_globals2 := global_write_word(t_globals1, G_WimpUSBPDev_Info(), vaddr2, WimpUSBPDev_ADDR_EMPTY_HIGH);
    var t_globals3 := global_write_word(t_globals2, G_WimpUSBPDev_Info(), vaddr3, PID_INVALID);
    var t_globals := global_write_word(t_globals3, G_WimpUSBPDev_Info(), vaddr4, WimpUSBPDev_Slot_UpdateFlag_Complete);

    forall i:uint32 | usbpdev_valid_slot_id(i) && i != slot
        ensures p_usbpdev_slot_equal(t_globals, new_globals, i)
    {
        // Dafny can automatically prove it
    }
    assert globals_other_gvar_unchanged(t_globals, new_globals, G_WimpUSBPDev_Info());

    if(!usbpdev_info_newvalue(old_globals, new_globals, slot, WimpUSBPDev_ADDR_EMPTY_LOW, WimpUSBPDev_ADDR_EMPTY_HIGH, PID_INVALID, WimpUSBPDev_Slot_UpdateFlag_Complete))
    {
        assert t_globals != new_globals;
        assert global_read_fullval(t_globals, G_WimpUSBPDev_Info()) != global_read_fullval(new_globals, G_WimpUSBPDev_Info());
        
        var i :| usbpdev_valid_slot_id(i) && !p_usbpdev_slot_equal(t_globals, new_globals, i);
        assert i == slot;

        assert false;
    }
}

// Prove the property 1 of <_usbpdev_set_slot>
lemma Lemma__usbpdev_set_slot_ProveProperty1(
    old_globals:globalsmap, globals1:globalsmap, new_globals:globalsmap, slot:word,
    new_usbpdev_addr_low:word, new_usbpdev_addr_high:word, new_pid:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbpdev_valid_slot_id(slot)

    requires var vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
            is_gvar_valid_addr(G_WimpUSBPDev_Info(), vaddr)

    requires usbpdev_info_newvalue(old_globals, globals1, slot, new_usbpdev_addr_low, new_usbpdev_addr_high, usbpdev_get_pid(old_globals, slot).v, WimpUSBPDev_Slot_UpdateFlag_Complete);
    
    requires var vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
            new_globals == global_write_word(globals1, G_WimpUSBPDev_Info(), vaddr, new_pid)

    ensures usbpdev_info_newvalue(old_globals, new_globals, slot, new_usbpdev_addr_low, new_usbpdev_addr_high, new_pid, WimpUSBPDev_Slot_UpdateFlag_Complete)
{
    reveal p_usbpdev_slot_equal();
    var old_pid := usbpdev_get_pid(old_globals, slot).v;

    // Prove other global variables are unchanged
    forall i:uint32 | usbpdev_valid_slot_id(i) && i != slot
        ensures p_usbpdev_slot_equal(old_globals, new_globals, i)
    {
        // Dafny can automatically prove it
    }
    assert globals_other_gvar_unchanged(old_globals, new_globals, G_WimpUSBPDev_Info());

    // Expand <new_globals> 
    var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset;
    var vaddr2 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset;
    var vaddr3 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
    var vaddr4 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;

    var globals1 := global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_usbpdev_addr_low);
    var t_new_globals2 := global_write_word(globals1, G_WimpUSBPDev_Info(), vaddr2, new_usbpdev_addr_high);
    var t_new_globals3 := global_write_word(t_new_globals2, G_WimpUSBPDev_Info(), vaddr3, old_pid);
    var t_new_globals4 := global_write_word(t_new_globals3, G_WimpUSBPDev_Info(), vaddr4, WimpUSBPDev_Slot_UpdateFlag_Complete);

    assert new_globals == global_write_word(t_new_globals4, G_WimpUSBPDev_Info(), vaddr3, new_pid);

    // Expand the post condition
    var t_globals1 := global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_usbpdev_addr_low);
    var t_globals2 := global_write_word(t_globals1, G_WimpUSBPDev_Info(), vaddr2, new_usbpdev_addr_high);
    var t_globals3 := global_write_word(t_globals2, G_WimpUSBPDev_Info(), vaddr3, new_pid);
    var t_globals := global_write_word(t_globals3, G_WimpUSBPDev_Info(), vaddr4, WimpUSBPDev_Slot_UpdateFlag_Complete);

    if(!usbpdev_info_newvalue(old_globals, new_globals, slot, new_usbpdev_addr_low, new_usbpdev_addr_high, new_pid, WimpUSBPDev_Slot_UpdateFlag_Complete))
    {
        assert t_globals != new_globals;
        assert global_read_fullval(t_globals, G_WimpUSBPDev_Info()) != global_read_fullval(new_globals, G_WimpUSBPDev_Info());
        
        // Show conflict
        var i :| usbpdev_valid_slot_id(i) && !p_usbpdev_slot_equal(t_globals, new_globals, i);
        assert i == slot;

        assert false;
    }
}

lemma Lemma_modify_regs_objects_stateeq_USBPDev_ActivateIntoWimpPartitions(old_s:state, new_s:state)
    requires WK_ValidMState(old_s.wk_mstate)
    requires WK_ValidMState(new_s.wk_mstate)

    requires new_s.wk_mstate.sregs == old_s.wk_mstate.sregs
    requires old_s.subjects == new_s.subjects &&
            old_s.objs_addrs == new_s.objs_addrs &&
            old_s.id_mappings == new_s.id_mappings &&
            old_s.activate_conds == new_s.activate_conds &&
            old_s.os_mem_active_map == new_s.os_mem_active_map &&
            old_s.ok == new_s.ok

    ensures va_state_eq(new_s, va_update_reg(EBP, new_s, va_update_reg(ESP, new_s,
        va_update_reg(EDI, new_s, va_update_reg(ESI, new_s, va_update_reg(EDX, new_s,
        va_update_reg(ECX, new_s, va_update_reg(EBX, new_s, va_update_reg(EAX, new_s,
        va_update_objects(new_s, va_update_globals(new_s, va_update_mem(new_s, va_update_ok(new_s,
        old_s)))))))))))))
{
    var s1 := va_update_objects(new_s, va_update_mem(new_s, va_update_ok(new_s, old_s)));

    assert s1.wk_mstate.m == new_s.wk_mstate.m;
    assert s1.objects == new_s.objects;
    assert s1.ok == new_s.ok;

    var s2 := va_update_reg(EBP, new_s, va_update_reg(ESP, new_s,
    va_update_reg(EDI, new_s, va_update_reg(ESI, new_s, va_update_reg(EDX, new_s,
    va_update_reg(ECX, new_s, va_update_reg(EBX, new_s, va_update_reg(EAX, new_s, s1))))))));

    assert s1.wk_mstate.m == s2.wk_mstate.m;
    assert s1.wk_mstate.globals == s2.wk_mstate.globals;
    assert s1.ok == s2.ok; 

    // Prove s2.wk_mstate.regs == new_s.wk_mstate.regs
    Lemma_EachRegsIsSameThenRegsAreSame(s2.wk_mstate.regs, new_s.wk_mstate.regs);
    assert s2.wk_mstate.regs == new_s.wk_mstate.regs;
}
