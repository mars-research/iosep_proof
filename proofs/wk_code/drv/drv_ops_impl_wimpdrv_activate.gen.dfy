include "drv_ops_impl.gen.dfy"
//-- WimpDrv_Activate_Impl

function method{:opaque} va_code_WimpDrv_Activate_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_pids_is_existing_wimp_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_CALL_WimpDrv_CheckDOPAddrRange(), va_CCons(va_code_Load(va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_CALL_PMem_AssignToWimps(), va_CCons(va_code_Load(va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code__wimpdrv_activate_private(), va_CCons(va_code_Load(va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP),
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(4 * ARCH_WORD_BYTES),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_op_word_reg(EAX)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES, va_op_word_reg(EBX)),
    va_CNil()))))))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpDrv_SlotID_EMPTY)), va_CNil())))), va_CNil()))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpDrv_SlotID_EMPTY)), va_CNil())))), va_CNil()))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpDrv_SlotID_EMPTY)), va_CNil())))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))
}

lemma{:timeLimitMultiplier 40} va_lemma_WimpDrv_Activate_Impl(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Activate_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 11 * ARCH_WORD_BYTES +
    WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 4 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space) && (var stack_params_space := 4 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var drv_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); drv_id !=
    WimpDrv_ID_RESERVED_EMPTY && WimpDrv_IDWord_ToDrvID(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, drv_id) in va_s0.subjects.wimp_drvs
  requires var new_wimpdrv_idword:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    var new_do_pbase:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); var new_do_pend:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); var drv_id:Drv_ID := WimpDrv_IDWord_ToDrvID(va_s0.subjects,
    va_s0.objects, va_s0.id_mappings, new_wimpdrv_idword); WK_ValidPMemRegion(new_do_pbase,
    new_do_pend) && wimpdrv_registration_info_must_exist(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, va_s0.objs_addrs, new_wimpdrv_idword, new_do_pbase, new_do_pend)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var drv_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES);
    var new_do_pbase:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); var new_do_pend:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP,
    va_s0)); var drv_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); (((((((ret == TRUE ==> pids_is_existing_wimp_pid(va_get_globals(va_s0),
    new_pid)) && (ret == TRUE ==> wimpdrv_valid_slot_id(drv_slot))) && (ret == TRUE ==> (forall
    i:word :: wimpdrv_valid_slot_id(i) ==> wimpdrv_get_id_word(va_get_globals(va_s0), i) !=
    drv_id))) && (ret == TRUE ==> wimpdrv_get_id_word(va_get_globals(va_s0), drv_slot) ==
    WimpDrv_ID_RESERVED_EMPTY)) && (ret == TRUE ==> wimpdrv_info_newvalue(va_get_globals(va_s0),
    va_get_globals(va_sM), drv_slot, drv_id, new_pid, new_do_pbase, new_do_pend,
    WimpDrv_Slot_UpdateFlag_Complete))) && (ret == TRUE ==>
    wimpdrv_DO_clear_non_mstate_relationship(va_s0, va_sM, drv_id))) && (ret != TRUE ==>
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
  reveal_va_code_WimpDrv_Activate_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b8, va_s8 := va_lemma_PUSH_VOID(va_b7, va_s7, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b9, va_s9 := va_lemma_Load(va_b8, va_s8, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b10, va_s10 := va_lemma_PUSH(va_b9, va_s9, va_sM, va_op_word_reg(EDI));
  ghost var va_b11, va_s11 := va_lemma_pids_is_existing_wimp_pid(va_b10, va_s10, va_sM);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0);
  ghost var va_b13, va_s13 := va_lemma_POP_VOID(va_b12, va_s12, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_Load(va_b16, va_s15, va_s14, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
    ghost var va_b18, va_s18 := va_lemma_PUSH(va_b17, va_s17, va_s14, va_op_word_reg(EDI));
    ghost var va_b19, va_s19 := va_lemma_Load(va_b18, va_s18, va_s14, va_op_word_reg(EDI),
      va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
    ghost var va_b20, va_s20 := va_lemma_PUSH(va_b19, va_s19, va_s14, va_op_word_reg(EDI));
    ghost var va_b21, va_s21 := va_lemma_CALL_WimpDrv_CheckDOPAddrRange(va_b20, va_s20, va_s14);
    ghost var va_b22, va_s22 := va_lemma_Load(va_b21, va_s21, va_s14, va_op_word_reg(EAX),
      va_op_word_reg(ESP), 0);
    ghost var va_b23, va_s23 := va_lemma_POP_VOID(va_b22, va_s22, va_s14, 2 * ARCH_WORD_BYTES);
    ghost var va_s24, va_c24, va_b24 := va_lemma_block(va_b23, va_s23, va_s14);
    ghost var va_cond_c24, va_s25:va_state := va_lemma_ifElse(va_get_ifCond(va_c24),
      va_get_ifTrue(va_c24), va_get_ifFalse(va_c24), va_s23, va_s24);
    if (va_cond_c24)
    {
      ghost var va_b26 := va_get_block(va_get_ifTrue(va_c24));
      reveal_p_ffi_wimpdrv_DO_check_paddr_range_retval();
      ghost var va_b28, va_s28 := va_lemma_Load(va_b26, va_s25, va_s24, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
      ghost var va_b29, va_s29 := va_lemma_PUSH(va_b28, va_s28, va_s24, va_op_word_reg(EDI));
      ghost var va_b30, va_s30 := va_lemma_Load(va_b29, va_s29, va_s24, va_op_word_reg(EDI),
        va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
      ghost var va_b31, va_s31 := va_lemma_PUSH(va_b30, va_s30, va_s24, va_op_word_reg(EDI));
      ghost var va_b32, va_s32 := va_lemma_CALL_PMem_AssignToWimps(va_b31, va_s31, va_s24);
      ghost var va_b33, va_s33 := va_lemma_Load(va_b32, va_s32, va_s24, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b34, va_s34 := va_lemma_POP_VOID(va_b33, va_s33, va_s24, 2 * ARCH_WORD_BYTES);
      ghost var va_s35, va_c35, va_b35 := va_lemma_block(va_b34, va_s34, va_s24);
      ghost var va_cond_c35, va_s36:va_state := va_lemma_ifElse(va_get_ifCond(va_c35),
        va_get_ifTrue(va_c35), va_get_ifFalse(va_c35), va_s34, va_s35);
      if (va_cond_c35)
      {
        ghost var va_b37 := va_get_block(va_get_ifTrue(va_c35));
        ghost var va_b38, va_s38 := va_lemma_Load(va_b37, va_s36, va_s35, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
        ghost var va_b39, va_s39 := va_lemma_PUSH(va_b38, va_s38, va_s35, va_op_word_reg(EDI));
        ghost var va_b40, va_s40 := va_lemma_Load(va_b39, va_s39, va_s35, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
        ghost var va_b41, va_s41 := va_lemma_PUSH(va_b40, va_s40, va_s35, va_op_word_reg(EDI));
        ghost var va_b42, va_s42 := va_lemma_Load(va_b41, va_s41, va_s35, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
        ghost var va_b43, va_s43 := va_lemma_PUSH(va_b42, va_s42, va_s35, va_op_word_reg(EDI));
        ghost var va_b44, va_s44 := va_lemma_Load(va_b43, va_s43, va_s35, va_op_word_reg(EDI),
          va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
        ghost var va_b45, va_s45 := va_lemma_PUSH(va_b44, va_s44, va_s35, va_op_word_reg(EDI));
        ghost var va_b46, va_s46 := va_lemma__wimpdrv_activate_private(va_b45, va_s45, va_s35);
        ghost var va_b47, va_s47 := va_lemma_Load(va_b46, va_s46, va_s35, va_op_word_reg(EAX),
          va_op_word_reg(ESP), 0);
        ghost var va_b48, va_s48 := va_lemma_Load(va_b47, va_s47, va_s35, va_op_word_reg(EBX),
          va_op_word_reg(ESP), ARCH_WORD_BYTES);
        ghost var va_b49, va_s49 := va_lemma_POP_VOID(va_b48, va_s48, va_s35, 4 * ARCH_WORD_BYTES);
        ghost var va_b50, va_s50 := va_lemma_Store(va_b49, va_s49, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_op_word_reg(EAX));
        ghost var va_b51, va_s51 := va_lemma_Store(va_b50, va_s50, va_s35, va_op_word_reg(EBP), 2 *
          ARCH_WORD_BYTES, va_op_word_reg(EBX));
        va_s35 := va_lemma_empty(va_s51, va_s35);
      }
      else
      {
        ghost var va_b52 := va_get_block(va_get_ifFalse(va_c35));
        ghost var va_b53, va_s53 := va_lemma_Store(va_b52, va_s36, va_s35, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        ghost var va_b54, va_s54 := va_lemma_Store(va_b53, va_s53, va_s35, va_op_word_reg(EBP), 2 *
          ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY));
        assert va_get_globals(va_s54) == va_get_globals(va_old_s);  // line 148 column 17 of file .\drv/drv_ops_impl_wimpdrv_activate.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s54));
        va_s35 := va_lemma_empty(va_s54, va_s35);
      }
      va_s24 := va_lemma_empty(va_s35, va_s24);
    }
    else
    {
      ghost var va_b57 := va_get_block(va_get_ifFalse(va_c24));
      ghost var va_b58, va_s58 := va_lemma_Store(va_b57, va_s25, va_s24, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b59, va_s59 := va_lemma_Store(va_b58, va_s58, va_s24, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY));
      assert va_get_globals(va_s59) == va_get_globals(va_old_s);  // line 157 column 13 of file .\drv/drv_ops_impl_wimpdrv_activate.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s59));
      va_s24 := va_lemma_empty(va_s59, va_s24);
    }
    va_s14 := va_lemma_empty(va_s24, va_s14);
  }
  else
  {
    ghost var va_b62 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b63, va_s63 := va_lemma_Store(va_b62, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b64, va_s64 := va_lemma_Store(va_b63, va_s63, va_s14, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY));
    assert va_get_globals(va_s64) == va_get_globals(va_old_s);  // line 166 column 9 of file .\drv/drv_ops_impl_wimpdrv_activate.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s64));
    va_s14 := va_lemma_empty(va_s64, va_s14);
  }
  ghost var va_b67, va_s67 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b68, va_s68 := va_lemma_POP_OneReg(va_b67, va_s67, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s68, va_sM);
}
//--
