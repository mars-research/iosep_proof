include "wk_partition_ops_utils.s.dfy"
include "partition_id_ops.gen.dfy"
include "dev/usb2/eehci_info.gen.dfy"
include "dev/usb2/usb_pdev_utils.gen.dfy"
include "dev/usb2/usb_tds_utils.gen.dfy"
include "drv/drv_ops_utils.gen.dfy"
include "transition_constraints.s.dfy"
include "proof\\wkapi_commutative_diagram.i.dfy"
//-- WK_EmptyPartitionCreate_Impl

function method{:opaque} va_code_WK_EmptyPartitionCreate_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ECX)), va_CCons(va_code_PUSH_VOID(1 *
    ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_const_word(PID_INVALID)),
    va_CCons(va_code_pid_existing_find_pid_slot(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP),
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(PID_GENERATE_FUNC_ERROR)), va_CNil()))),
    va_Block(va_CCons(va_code_pid_generate(va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(PID_GENERATE_FUNC_ERROR)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(PID_GENERATE_FUNC_ERROR)), va_CNil()))),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_pid_existing_write_pid(),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_op_word_reg(EAX)), va_CNil())))))))), va_CNil())))),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))
}

lemma{:timeLimitMultiplier 5} va_lemma_WK_EmptyPartitionCreate_Impl(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state, pid_slot:word)
  requires va_require(va_b0, va_code_WK_EmptyPartitionCreate_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 13 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var new_pid:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    ((ret == TRUE ==> (!(WS_PartitionID(new_pid) in pids_parse_g_wimp_pids(va_get_globals(va_s0)))
    && new_pid != PID_INVALID) && new_pid != PID_RESERVED_OS_PARTITION) && (ret == TRUE ==>
    wk_create_partition_globalvars_relation(va_get_globals(va_s0), va_get_globals(va_sM), pid_slot,
    new_pid))) && (ret != TRUE ==> global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0),
    va_get_globals(va_sM)))
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
  ensures  va_state_eq(va_sM, va_update_globals(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI,
    va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_WK_EmptyPartitionCreate_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EBX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ECX));
  ghost var va_b9, va_s9 := va_lemma_PUSH_VOID(va_b8, va_s8, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b10, va_s10 := va_lemma_PUSH(va_b9, va_s9, va_sM, va_const_word(PID_INVALID));
  ghost var va_b11, va_s11 := va_lemma_pid_existing_find_pid_slot(va_b10, va_s10, va_sM);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0);
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(ESP), ARCH_WORD_BYTES);
  ghost var va_b14, va_s14 := va_lemma_POP_VOID(va_b13, va_s13, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s15, va_c15, va_b15 := va_lemma_block(va_b14, va_s14, va_sM);
  ghost var va_cond_c15, va_s16:va_state := va_lemma_ifElse(va_get_ifCond(va_c15),
    va_get_ifTrue(va_c15), va_get_ifFalse(va_c15), va_s14, va_s15);
  if (va_cond_c15)
  {
    ghost var va_b17 := va_get_block(va_get_ifTrue(va_c15));
    ghost var va_b18, va_s18 := va_lemma_Store(va_b17, va_s16, va_s15, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b19, va_s19 := va_lemma_Store(va_b18, va_s18, va_s15, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(PID_GENERATE_FUNC_ERROR));
    assert va_get_globals(va_s19) == va_get_globals(va_old_s);  // line 89 column 9 of file .\wk_partition_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s19));
    va_s15 := va_lemma_empty(va_s19, va_s15);
  }
  else
  {
    ghost var va_b22 := va_get_block(va_get_ifFalse(va_c15));
    ghost var va_b23, va_s23 := va_lemma_pid_generate(va_b22, va_s16, va_s15, va_op_reg_reg(EAX));
    ghost var va_s24, va_c24, va_b24 := va_lemma_block(va_b23, va_s23, va_s15);
    ghost var va_cond_c24, va_s25:va_state := va_lemma_ifElse(va_get_ifCond(va_c24),
      va_get_ifTrue(va_c24), va_get_ifFalse(va_c24), va_s23, va_s24);
    if (va_cond_c24)
    {
      ghost var va_b26 := va_get_block(va_get_ifTrue(va_c24));
      ghost var va_b27, va_s27 := va_lemma_Store(va_b26, va_s25, va_s24, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b28, va_s28 := va_lemma_Store(va_b27, va_s27, va_s24, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_const_word(PID_GENERATE_FUNC_ERROR));
      assert va_get_globals(va_s28) == va_get_globals(va_old_s);  // line 103 column 13 of file .\wk_partition_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s28));
      va_s24 := va_lemma_empty(va_s28, va_s24);
    }
    else
    {
      ghost var va_b31 := va_get_block(va_get_ifFalse(va_c24));
      assert va_get_reg(EAX, va_s25) <= pids_parse_g_pid_counter(va_get_globals(va_s25)).v;  // line 108 column 13 of file .\wk_partition_ops_impl.vad
      ghost var ghost_find_slot := va_get_reg(EBX, va_s25);
      ghost var va_b34, va_s34 := va_lemma_PUSH(va_b31, va_s25, va_s24, va_op_word_reg(EAX));
      ghost var va_b35, va_s35 := va_lemma_PUSH(va_b34, va_s34, va_s24, va_op_word_reg(EBX));
      ghost var va_b36, va_s36 := va_lemma_pid_existing_write_pid(va_b35, va_s35, va_s24);
      ghost var va_b37, va_s37 := va_lemma_POP_VOID(va_b36, va_s36, va_s24, 2 * ARCH_WORD_BYTES);
      pid_slot := ghost_find_slot;
      ghost var va_b39, va_s39 := va_lemma_Store(va_b37, va_s37, va_s24, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      ghost var va_b40, va_s40 := va_lemma_Store(va_b39, va_s39, va_s24, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_op_word_reg(EAX));
      va_s24 := va_lemma_empty(va_s40, va_s24);
    }
    va_s15 := va_lemma_empty(va_s24, va_s15);
  }
  ghost var va_b41, va_s41 := va_lemma_POP_OneReg(va_b15, va_s15, va_sM, va_op_reg_reg(ECX));
  ghost var va_b42, va_s42 := va_lemma_POP_TwoRegs(va_b41, va_s41, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EBX));
  ghost var va_b43, va_s43 := va_lemma_POP_OneReg(va_b42, va_s42, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s43, va_sM);
}
//--
//-- WK_EmptyPartitionDestroy_Impl

function method{:opaque} va_code_WK_EmptyPartitionDestroy_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ECX)), va_CCons(va_code_PUSH_VOID(1 *
    ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(EBP),
    ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EAX)),
    va_CCons(va_code_pids_is_existing_wimp_pid(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP),
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_eehci_find_slot_in_partition(),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbpdev_find_slot_in_partition(),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_usbtd_find_slot_in_partition(),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_wimpdrv_find_slot_in_partition(),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_PUSH(va_const_word(PID_INVALID)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_pid_existing_write_pid_invalid(),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(TRUE)), va_CNil())))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))
}

lemma{:timeLimitMultiplier 70} va_lemma_WK_EmptyPartitionDestroy_Impl(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WK_EmptyPartitionDestroy_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 19 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var ret:word
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); (((ret == TRUE ==>
    pids_is_existing_wimp_pid(va_get_globals(va_s0), pid)) && (ret == TRUE ==> (((forall i:word ::
    eehci_valid_slot_id(i) ==> eehci_info_get_pid(va_get_globals(va_s0), i) != WS_PartitionID(pid))
    && (forall i:word :: usbpdev_valid_slot_id(i) ==> usbpdev_get_pid(va_get_globals(va_s0), i) !=
    WS_PartitionID(pid))) && (forall i:word :: usbtd_map_valid_slot_id(i) ==>
    usbtd_map_get_pid(va_get_globals(va_s0), i) != WS_PartitionID(pid))) && (forall i:word ::
    wimpdrv_valid_slot_id(i) ==> wimpdrv_get_pid(va_get_globals(va_s0), i) !=
    WS_PartitionID(pid)))) && (ret == TRUE ==>
    wk_destroy_partition_globalvars_relation(va_get_globals(va_s0), va_get_globals(va_sM), pid)))
    && (ret != TRUE ==> global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0),
    va_get_globals(va_sM)))
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 1 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_globals(va_sM, va_update_reg(EDI, va_sM, va_update_reg(ESI,
    va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_WK_EmptyPartitionDestroy_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EBX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(ECX));
  ghost var in_pid := stack_get_val(va_get_mem(va_old_s), va_get_reg(ESP, va_old_s));
  ghost var va_b10, va_s10 := va_lemma_PUSH_VOID(va_b8, va_s8, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_PUSH(va_b11, va_s11, va_sM, va_op_word_reg(EAX));
  ghost var va_b13, va_s13 := va_lemma_pids_is_existing_wimp_pid(va_b12, va_s12, va_sM);
  ghost var va_b14, va_s14 := va_lemma_Load(va_b13, va_s13, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0);
  ghost var va_b15, va_s15 := va_lemma_Load(va_b14, va_s14, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(ESP), ARCH_WORD_BYTES);
  ghost var va_b16, va_s16 := va_lemma_POP_VOID(va_b15, va_s15, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s17, va_c17, va_b17 := va_lemma_block(va_b16, va_s16, va_sM);
  ghost var va_cond_c17, va_s18:va_state := va_lemma_ifElse(va_get_ifCond(va_c17),
    va_get_ifTrue(va_c17), va_get_ifFalse(va_c17), va_s16, va_s17);
  if (va_cond_c17)
  {
    ghost var va_b19 := va_get_block(va_get_ifTrue(va_c17));
    ghost var va_b20, va_s20 := va_lemma_PUSH_VOID(va_b19, va_s18, va_s17, 1 * ARCH_WORD_BYTES);
    ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s20, va_s17, va_op_word_reg(EAX));
    ghost var va_b22, va_s22 := va_lemma_eehci_find_slot_in_partition(va_b21, va_s21, va_s17);
    ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s17, va_op_word_reg(ECX),
      va_op_word_reg(ESP), 0);
    ghost var va_b24, va_s24 := va_lemma_POP_VOID(va_b23, va_s23, va_s17, 2 * ARCH_WORD_BYTES);
    ghost var va_s25, va_c25, va_b25 := va_lemma_block(va_b24, va_s24, va_s17);
    ghost var va_cond_c25, va_s26:va_state := va_lemma_ifElse(va_get_ifCond(va_c25),
      va_get_ifTrue(va_c25), va_get_ifFalse(va_c25), va_s24, va_s25);
    if (va_cond_c25)
    {
      ghost var va_b27 := va_get_block(va_get_ifTrue(va_c25));
      ghost var va_b28, va_s28 := va_lemma_PUSH_VOID(va_b27, va_s26, va_s25, 1 * ARCH_WORD_BYTES);
      ghost var va_b29, va_s29 := va_lemma_PUSH(va_b28, va_s28, va_s25, va_op_word_reg(EAX));
      ghost var va_b30, va_s30 := va_lemma_usbpdev_find_slot_in_partition(va_b29, va_s29, va_s25);
      ghost var va_b31, va_s31 := va_lemma_Load(va_b30, va_s30, va_s25, va_op_word_reg(ECX),
        va_op_word_reg(ESP), 0);
      ghost var va_b32, va_s32 := va_lemma_POP_VOID(va_b31, va_s31, va_s25, 2 * ARCH_WORD_BYTES);
      ghost var va_s33, va_c33, va_b33 := va_lemma_block(va_b32, va_s32, va_s25);
      ghost var va_cond_c33, va_s34:va_state := va_lemma_ifElse(va_get_ifCond(va_c33),
        va_get_ifTrue(va_c33), va_get_ifFalse(va_c33), va_s32, va_s33);
      if (va_cond_c33)
      {
        ghost var va_b35 := va_get_block(va_get_ifTrue(va_c33));
        ghost var va_b36, va_s36 := va_lemma_PUSH_VOID(va_b35, va_s34, va_s33, 1 * ARCH_WORD_BYTES);
        ghost var va_b37, va_s37 := va_lemma_PUSH(va_b36, va_s36, va_s33, va_op_word_reg(EAX));
        ghost var va_b38, va_s38 := va_lemma_usbtd_find_slot_in_partition(va_b37, va_s37, va_s33);
        ghost var va_b39, va_s39 := va_lemma_Load(va_b38, va_s38, va_s33, va_op_word_reg(ECX),
          va_op_word_reg(ESP), 0);
        ghost var va_b40, va_s40 := va_lemma_POP_VOID(va_b39, va_s39, va_s33, 2 * ARCH_WORD_BYTES);
        ghost var va_s41, va_c41, va_b41 := va_lemma_block(va_b40, va_s40, va_s33);
        ghost var va_cond_c41, va_s42:va_state := va_lemma_ifElse(va_get_ifCond(va_c41),
          va_get_ifTrue(va_c41), va_get_ifFalse(va_c41), va_s40, va_s41);
        if (va_cond_c41)
        {
          ghost var va_b43 := va_get_block(va_get_ifTrue(va_c41));
          ghost var va_b44, va_s44 := va_lemma_PUSH_VOID(va_b43, va_s42, va_s41, 1 *
            ARCH_WORD_BYTES);
          ghost var va_b45, va_s45 := va_lemma_PUSH(va_b44, va_s44, va_s41, va_op_word_reg(EAX));
          ghost var va_b46, va_s46 := va_lemma_wimpdrv_find_slot_in_partition(va_b45, va_s45,
            va_s41);
          ghost var va_b47, va_s47 := va_lemma_Load(va_b46, va_s46, va_s41, va_op_word_reg(ECX),
            va_op_word_reg(ESP), 0);
          ghost var va_b48, va_s48 := va_lemma_POP_VOID(va_b47, va_s47, va_s41, 2 *
            ARCH_WORD_BYTES);
          ghost var va_s49, va_c49, va_b49 := va_lemma_block(va_b48, va_s48, va_s41);
          ghost var va_cond_c49, va_s50:va_state := va_lemma_ifElse(va_get_ifCond(va_c49),
            va_get_ifTrue(va_c49), va_get_ifFalse(va_c49), va_s48, va_s49);
          if (va_cond_c49)
          {
            ghost var va_b51 := va_get_block(va_get_ifTrue(va_c49));
            ghost var va_b52, va_s52 := va_lemma_PUSH(va_b51, va_s50, va_s49,
              va_const_word(PID_INVALID));
            ghost var va_b53, va_s53 := va_lemma_PUSH(va_b52, va_s52, va_s49, va_op_word_reg(EBX));
            ghost var va_b54, va_s54 := va_lemma_pid_existing_write_pid_invalid(va_b53, va_s53,
              va_s49);
            ghost var va_b55, va_s55 := va_lemma_POP_VOID(va_b54, va_s54, va_s49, 2 *
              ARCH_WORD_BYTES);
            ghost var va_b56, va_s56 := va_lemma_Store(va_b55, va_s55, va_s49, va_op_word_reg(EBP),
              ARCH_WORD_BYTES, va_const_word(TRUE));
            va_s49 := va_lemma_empty(va_s56, va_s49);
          }
          else
          {
            ghost var va_b57 := va_get_block(va_get_ifFalse(va_c49));
            ghost var va_b58, va_s58 := va_lemma_Store(va_b57, va_s50, va_s49, va_op_word_reg(EBP),
              ARCH_WORD_BYTES, va_const_word(FALSE));
            assert va_get_globals(va_s58) == va_get_globals(va_old_s);  // line 257 column 25 of file .\wk_partition_ops_impl.vad
            Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
              va_get_globals(va_s58));
            va_s49 := va_lemma_empty(va_s58, va_s49);
          }
          va_s41 := va_lemma_empty(va_s49, va_s41);
        }
        else
        {
          ghost var va_b61 := va_get_block(va_get_ifFalse(va_c41));
          ghost var va_b62, va_s62 := va_lemma_Store(va_b61, va_s42, va_s41, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s62) == va_get_globals(va_old_s);  // line 264 column 21 of file .\wk_partition_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s62));
          va_s41 := va_lemma_empty(va_s62, va_s41);
        }
        va_s33 := va_lemma_empty(va_s41, va_s33);
      }
      else
      {
        ghost var va_b65 := va_get_block(va_get_ifFalse(va_c33));
        ghost var va_b66, va_s66 := va_lemma_Store(va_b65, va_s34, va_s33, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s66) == va_get_globals(va_old_s);  // line 271 column 17 of file .\wk_partition_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s66));
        va_s33 := va_lemma_empty(va_s66, va_s33);
      }
      va_s25 := va_lemma_empty(va_s33, va_s25);
    }
    else
    {
      ghost var va_b69 := va_get_block(va_get_ifFalse(va_c25));
      ghost var va_b70, va_s70 := va_lemma_Store(va_b69, va_s26, va_s25, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s70) == va_get_globals(va_old_s);  // line 278 column 13 of file .\wk_partition_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s70));
      va_s25 := va_lemma_empty(va_s70, va_s25);
    }
    va_s17 := va_lemma_empty(va_s25, va_s17);
  }
  else
  {
    ghost var va_b73 := va_get_block(va_get_ifFalse(va_c17));
    ghost var va_b74, va_s74 := va_lemma_Store(va_b73, va_s18, va_s17, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s74) == va_get_globals(va_old_s);  // line 285 column 9 of file .\wk_partition_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s74));
    va_s17 := va_lemma_empty(va_s74, va_s17);
  }
  ghost var va_b77, va_s77 := va_lemma_POP_OneReg(va_b17, va_s17, va_sM, va_op_reg_reg(ECX));
  ghost var va_b78, va_s78 := va_lemma_POP_TwoRegs(va_b77, va_s77, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EBX));
  ghost var va_b79, va_s79 := va_lemma_POP_OneReg(va_b78, va_s78, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s79, va_sM);
}
//--
