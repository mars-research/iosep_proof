include "drv_ops_utils.gen.dfy"
include "../partition_id_ops.gen.dfy"
include "../dev/usb2/usb_tds_ops/usb_tds_ops.private.gen.dfy"
include "drv_ops_utils.i.dfy"
include "public\\wimpdrv_lemmas.i.dfy"
//-- _wimpdrv_activate_private
//--
//-- WimpDrv_Deactivate_Impl

function method{:opaque} va_code_WimpDrv_Deactivate_Impl():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_wimpdrv_check_slotid(va_op_reg_reg(EDI), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_wimpdrv_ops_get_updateflag_nocheck(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX),
    va_const_cmp(WimpDrv_Slot_UpdateFlag_Complete)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_wimpdrv_ops_get_pid_nocheck(), va_CCons(va_code_Load(va_op_word_reg(EDX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDX)),
    va_CCons(va_code_pids_is_existing_wimp_pid(), va_CCons(va_code_Load(va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code__wimpdrv_find_referencing_secure_usbtd(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_wimpdrv_ops_get_do_paddr_region_no_check(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), ARCH_WORD_BYTES),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_IMM(0),
    va_CCons(va_code_PUSH_IMM(0), va_CCons(va_code_PUSH_IMM(PID_INVALID),
    va_CCons(va_code_PUSH_IMM(WimpDrv_ID_RESERVED_EMPTY),
    va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code__wimpdrv_update_slot_pid_to_invalid(), va_CCons(va_code_POP_VOID(5 *
    ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_CALL_PMem_ReleaseFromWimps(),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES), va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(TRUE)), va_CNil()))))))))))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil()))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))
}

lemma{:timeLimitMultiplier 90} va_lemma_WimpDrv_Deactivate_Impl(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_WimpDrv_Deactivate_Impl(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ +
    FFI_PMem_ReleaseFromWimps_StackParamsWords * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP,
    va_s0) - stack_req_space) && (var stack_params_space := 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var drv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    wimpdrv_valid_slot_id(drv_slot) && pids_is_existing_wimp_pid(va_get_globals(va_s0),
    wimpdrv_get_pid(va_get_globals(va_s0), drv_slot).v) ==> (var wimpdrv_idword :=
    wimpdrv_get_id_word(va_get_globals(va_s0), drv_slot); var wimpdrv_id:Drv_ID :=
    WimpDrv_IDWord_ToDrvID(va_s0.subjects, va_s0.objects, va_s0.id_mappings, wimpdrv_idword);
    wimpdrv_id in va_s0.subjects.wimp_drvs)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var drv_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    ret:uint32 := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ((((((ret == TRUE ==>
    wimpdrv_valid_slot_id(drv_slot)) && (ret == TRUE ==>
    pids_is_existing_wimp_pid(va_get_globals(va_s0), wimpdrv_get_pid(va_get_globals(va_s0),
    drv_slot).v))) && (ret == TRUE ==> wimpdrv_do_get_flag(va_get_globals(va_s0), drv_slot) ==
    WimpDrv_Slot_UpdateFlag_Complete)) && (ret == TRUE ==>
    usbtds_verifiedtds_do_not_associate_wimpdrv(va_get_globals(va_s0), drv_slot))) && (ret == TRUE
    ==> wimpdrv_get_pid(va_get_globals(va_sM), drv_slot) == WS_PartitionID(PID_INVALID))) && (ret
    == TRUE ==> wimpdrv_info_newvalue(va_get_globals(va_s0), va_get_globals(va_sM), drv_slot,
    WimpDrv_ID_RESERVED_EMPTY, PID_INVALID, 0, 0, WimpDrv_Slot_UpdateFlag_Complete))) && (ret !=
    TRUE ==> global_non_scratchpad_vars_are_unchanged(va_get_globals(va_s0), va_get_globals(va_sM)))
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
  reveal_va_code_WimpDrv_Deactivate_Impl();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var in_slot_id := va_get_reg(EDI, va_s11);
  ghost var va_b13, va_s13 := va_lemma_wimpdrv_check_slotid(va_b11, va_s11, va_sM,
    va_op_reg_reg(EDI), va_op_reg_reg(EAX));
  ghost var va_s14, va_c14, va_b14 := va_lemma_block(va_b13, va_s13, va_sM);
  ghost var va_cond_c14, va_s15:va_state := va_lemma_ifElse(va_get_ifCond(va_c14),
    va_get_ifTrue(va_c14), va_get_ifFalse(va_c14), va_s13, va_s14);
  if (va_cond_c14)
  {
    ghost var va_b16 := va_get_block(va_get_ifTrue(va_c14));
    ghost var va_b17, va_s17 := va_lemma_PUSH(va_b16, va_s15, va_s14, va_op_word_reg(EDI));
    ghost var va_b18, va_s18 := va_lemma_wimpdrv_ops_get_updateflag_nocheck(va_b17, va_s17, va_s14);
    ghost var va_b19, va_s19 := va_lemma_Load(va_b18, va_s18, va_s14, va_op_word_reg(EAX),
      va_op_word_reg(ESP), 0);
    ghost var va_b20, va_s20 := va_lemma_POP_VOID(va_b19, va_s19, va_s14, 1 * ARCH_WORD_BYTES);
    ghost var va_s21, va_c21, va_b21 := va_lemma_block(va_b20, va_s20, va_s14);
    ghost var va_cond_c21, va_s22:va_state := va_lemma_ifElse(va_get_ifCond(va_c21),
      va_get_ifTrue(va_c21), va_get_ifFalse(va_c21), va_s20, va_s21);
    if (va_cond_c21)
    {
      ghost var va_b23 := va_get_block(va_get_ifTrue(va_c21));
      ghost var va_b24, va_s24 := va_lemma_PUSH(va_b23, va_s22, va_s21, va_op_word_reg(EDI));
      ghost var va_b25, va_s25 := va_lemma_wimpdrv_ops_get_pid_nocheck(va_b24, va_s24, va_s21);
      ghost var va_b26, va_s26 := va_lemma_Load(va_b25, va_s25, va_s21, va_op_word_reg(EDX),
        va_op_word_reg(ESP), 0);
      ghost var va_b27, va_s27 := va_lemma_POP_VOID(va_b26, va_s26, va_s21, 1 * ARCH_WORD_BYTES);
      ghost var va_b28, va_s28 := va_lemma_PUSH_VOID(va_b27, va_s27, va_s21, 1 * ARCH_WORD_BYTES);
      ghost var va_b29, va_s29 := va_lemma_PUSH(va_b28, va_s28, va_s21, va_op_word_reg(EDX));
      ghost var va_b30, va_s30 := va_lemma_pids_is_existing_wimp_pid(va_b29, va_s29, va_s21);
      ghost var va_b31, va_s31 := va_lemma_Load(va_b30, va_s30, va_s21, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b32, va_s32 := va_lemma_POP_VOID(va_b31, va_s31, va_s21, 2 * ARCH_WORD_BYTES);
      ghost var va_s33, va_c33, va_b33 := va_lemma_block(va_b32, va_s32, va_s21);
      ghost var va_cond_c33, va_s34:va_state := va_lemma_ifElse(va_get_ifCond(va_c33),
        va_get_ifTrue(va_c33), va_get_ifFalse(va_c33), va_s32, va_s33);
      if (va_cond_c33)
      {
        ghost var va_b35 := va_get_block(va_get_ifTrue(va_c33));
        Lemma_WimpDrv_ExistInSystem_IfRegisteredAndActive(va_s34.subjects, va_s34.objects,
          va_s34.id_mappings, va_s34.objs_addrs, va_get_globals(va_s34), in_slot_id);
        ghost var va_b37, va_s37 := va_lemma_PUSH_VOID(va_b35, va_s34, va_s33, 1 * ARCH_WORD_BYTES);
        ghost var va_b38, va_s38 := va_lemma_PUSH(va_b37, va_s37, va_s33, va_op_word_reg(EDI));
        ghost var va_b39, va_s39 := va_lemma__wimpdrv_find_referencing_secure_usbtd(va_b38, va_s38,
          va_s33);
        ghost var va_b40, va_s40 := va_lemma_Load(va_b39, va_s39, va_s33, va_op_word_reg(EAX),
          va_op_word_reg(ESP), 0);
        ghost var va_b41, va_s41 := va_lemma_POP_VOID(va_b40, va_s40, va_s33, 2 * ARCH_WORD_BYTES);
        ghost var va_s42, va_c42, va_b42 := va_lemma_block(va_b41, va_s41, va_s33);
        ghost var va_cond_c42, va_s43:va_state := va_lemma_ifElse(va_get_ifCond(va_c42),
          va_get_ifTrue(va_c42), va_get_ifFalse(va_c42), va_s41, va_s42);
        if (va_cond_c42)
        {
          ghost var va_b44 := va_get_block(va_get_ifTrue(va_c42));
          assert usbtds_verifiedtds_do_not_associate_wimpdrv(va_get_globals(va_old_s),
            va_get_reg(EDI, va_s43));  // line 133 column 21 of file .\drv/drv_ops_impl.vad
          ghost var va_b46, va_s46 := va_lemma_PUSH_VOID(va_b44, va_s43, va_s42, 1 *
            ARCH_WORD_BYTES);
          ghost var va_b47, va_s47 := va_lemma_PUSH(va_b46, va_s46, va_s42, va_op_word_reg(EDI));
          ghost var va_b48, va_s48 := va_lemma_wimpdrv_ops_get_do_paddr_region_no_check(va_b47,
            va_s47, va_s42);
          ghost var va_b49, va_s49 := va_lemma_Load(va_b48, va_s48, va_s42, va_op_word_reg(EBX),
            va_op_word_reg(ESP), 0);
          ghost var va_b50, va_s50 := va_lemma_Load(va_b49, va_s49, va_s42, va_op_word_reg(ECX),
            va_op_word_reg(ESP), ARCH_WORD_BYTES);
          ghost var va_b51, va_s51 := va_lemma_POP_VOID(va_b50, va_s50, va_s42, 2 *
            ARCH_WORD_BYTES);
          ghost var this1 := va_s51;
          ghost var globals1 := va_get_globals(va_s51);
          assert globals1 == va_get_globals(va_old_s);  // line 144 column 21 of file .\drv/drv_ops_impl.vad
          ghost var va_b55, va_s55 := va_lemma_PUSH_IMM(va_b51, va_s51, va_s42, 0);
          ghost var va_b56, va_s56 := va_lemma_PUSH_IMM(va_b55, va_s55, va_s42, 0);
          ghost var va_b57, va_s57 := va_lemma_PUSH_IMM(va_b56, va_s56, va_s42, PID_INVALID);
          ghost var va_b58, va_s58 := va_lemma_PUSH_IMM(va_b57, va_s57, va_s42,
            WimpDrv_ID_RESERVED_EMPTY);
          ghost var va_b59, va_s59 := va_lemma_PUSH(va_b58, va_s58, va_s42, va_op_word_reg(EDI));
          ghost var va_b60, va_s60 := va_lemma__wimpdrv_update_slot_pid_to_invalid(va_b59, va_s59,
            va_s42);
          ghost var va_b61, va_s61 := va_lemma_POP_VOID(va_b60, va_s60, va_s42, 5 *
            ARCH_WORD_BYTES);
          ghost var globals2 := va_get_globals(va_s61);
          Lemma_usbtds_verifiedtds_do_not_associate_wimpdrv_HoldIfUSBTDsAreUnchanged(globals1,
            globals2, va_get_reg(EDI, va_s61));
          assert usbtds_verifiedtds_do_not_associate_wimpdrv(globals2, va_get_reg(EDI, va_s61)); 
            // line 156 column 21 of file .\drv/drv_ops_impl.vad
          Lemma_wimpdrv_info_newvalue_ProveOtherGVarsAreUnmodified(globals1,
            va_get_globals(va_s61), va_get_reg(EDI, va_s61), WimpDrv_ID_RESERVED_EMPTY,
            PID_INVALID, 0, 0, WimpDrv_Slot_UpdateFlag_Complete);
          Lemma_wimpdrv_info_newvalue_ProveOtherWimpDrvSlotsAreUnmodified(globals1,
            va_get_globals(va_s61), va_get_reg(EDI, va_s61), WimpDrv_ID_RESERVED_EMPTY,
            PID_INVALID, 0, 0, WimpDrv_Slot_UpdateFlag_Complete);
          Lemma_WimpDrv_Deactivate_ProveNoActiveWimpDrvOverlapWithDeactivatedPMemRegion(this1,
            va_s61, va_get_reg(EDI, va_s61), va_get_reg(EBX, va_s61), va_get_reg(ECX, va_s61));
          ghost var va_b68, va_s68 := va_lemma_PUSH(va_b61, va_s61, va_s42, va_op_word_reg(ECX));
          ghost var va_b69, va_s69 := va_lemma_PUSH(va_b68, va_s68, va_s42, va_op_word_reg(EBX));
          ghost var va_b70, va_s70 := va_lemma_CALL_PMem_ReleaseFromWimps(va_b69, va_s69, va_s42);
          ghost var va_b71, va_s71 := va_lemma_POP_VOID(va_b70, va_s70, va_s42, 2 *
            ARCH_WORD_BYTES);
          ghost var va_b72, va_s72 := va_lemma_Store(va_b71, va_s71, va_s42, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(TRUE));
          Lemma_usbtds_verifiedtds_do_not_associate_wimpdrv_HoldIfUSBTDsAreUnchanged(globals2,
            va_get_globals(va_s72), in_slot_id);
          assert usbtds_verifiedtds_do_not_associate_wimpdrv(va_get_globals(va_s72), in_slot_id); 
            // line 172 column 21 of file .\drv/drv_ops_impl.vad
          Lemma_usbtds_verifiedtds_do_not_associate_wimpdrv_HoldIfUSBTDsAreUnchanged(va_get_globals(va_s72),
            va_get_globals(va_old_s), in_slot_id);
          assert usbtds_verifiedtds_do_not_associate_wimpdrv(va_get_globals(va_old_s), in_slot_id);
            // line 174 column 21 of file .\drv/drv_ops_impl.vad
          va_s42 := va_lemma_empty(va_s72, va_s42);
        }
        else
        {
          ghost var va_b77 := va_get_block(va_get_ifFalse(va_c42));
          ghost var va_b78, va_s78 := va_lemma_Store(va_b77, va_s43, va_s42, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          assert va_get_globals(va_s78) == va_get_globals(va_old_s);  // line 180 column 21 of file .\drv/drv_ops_impl.vad
          Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
            va_get_globals(va_s78));
          va_s42 := va_lemma_empty(va_s78, va_s42);
        }
        va_s33 := va_lemma_empty(va_s42, va_s33);
      }
      else
      {
        ghost var va_b81 := va_get_block(va_get_ifFalse(va_c33));
        ghost var va_b82, va_s82 := va_lemma_Store(va_b81, va_s34, va_s33, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        assert va_get_globals(va_s82) == va_get_globals(va_old_s);  // line 188 column 17 of file .\drv/drv_ops_impl.vad
        Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
          va_get_globals(va_s82));
        va_s33 := va_lemma_empty(va_s82, va_s33);
      }
      va_s21 := va_lemma_empty(va_s33, va_s21);
    }
    else
    {
      ghost var va_b85 := va_get_block(va_get_ifFalse(va_c21));
      ghost var va_b86, va_s86 := va_lemma_Store(va_b85, va_s22, va_s21, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      assert va_get_globals(va_s86) == va_get_globals(va_old_s);  // line 196 column 13 of file .\drv/drv_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s86));
      va_s21 := va_lemma_empty(va_s86, va_s21);
    }
    va_s14 := va_lemma_empty(va_s21, va_s14);
  }
  else
  {
    ghost var va_b89 := va_get_block(va_get_ifFalse(va_c14));
    ghost var va_b90, va_s90 := va_lemma_Store(va_b89, va_s15, va_s14, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    assert va_get_globals(va_s90) == va_get_globals(va_old_s);  // line 204 column 9 of file .\drv/drv_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s90));
    va_s14 := va_lemma_empty(va_s90, va_s14);
  }
  ghost var va_b93, va_s93 := va_lemma_POP_Reg1ToReg6(va_b14, va_s14, va_sM);
  ghost var va_b94, va_s94 := va_lemma_POP_OneReg(va_b93, va_s93, va_sM, va_op_reg_reg(EBP));
  Lemma_modify_regs_stateeq(va_old_s, va_s94);
  va_sM := va_lemma_empty(va_s94, va_sM);
}
//--
//-- _wimpdrv_activate_private

function method{:opaque} va_code__wimpdrv_activate_private():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EBX), va_op_reg_reg(ECX)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EDX)), va_CCons(va_code_PUSH_VOID(1 *
    ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 1 *
    ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDX)),
    va_CCons(va_code__wimpdrv_find_slot_by_id(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(FALSE)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_const_word(WimpDrv_ID_RESERVED_EMPTY)),
    va_CCons(va_code__wimpdrv_find_slot_by_id(), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP),
    ARCH_WORD_BYTES), va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_Load(va_op_word_reg(EDX),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDX)),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_Load(va_op_word_reg(EDX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDX)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code__wimpdrv_update_slot_pid_to_valid(), va_CCons(va_code_POP_VOID(5 *
    ARCH_WORD_BYTES), va_CCons(va_code_PUSH_Reg1ToReg6(),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_CALL_WimpDrv_DO_Clear(),
    va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES, va_op_word_reg(EBX)),
    va_CNil()))))))))))))))))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY)), va_CNil())))), va_CNil())))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(WimpDrv_SlotID_EMPTY)), va_CNil())))),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EBX), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))
}

lemma{:timeLimitMultiplier 70} va_lemma__wimpdrv_activate_private(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__wimpdrv_activate_private(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + WK_STACK_FOR_EXTERNEL_FUNCS_SZ + 1 *
    ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space)
    && (var stack_params_space := 4 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) +
    stack_params_space - ARCH_WORD_BYTES))
  requires var drv_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); drv_id !=
    WimpDrv_ID_RESERVED_EMPTY && WimpDrv_IDWord_ToDrvID(va_s0.subjects, va_s0.objects,
    va_s0.id_mappings, drv_id) in va_s0.subjects.wimp_drvs
  requires var new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var new_do_pbase:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var new_do_pend:word := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES); (WS_PartitionID(new_pid) in
    pids_parse_g_wimp_pids(va_get_globals(va_s0)) && WK_ValidPMemRegion(new_do_pbase, new_do_pend))
    && (forall i:uint32 :: (wimpdrv_valid_slot_id(i) && wimpdrv_do_get_flag(va_get_globals(va_s0),
    i) == WimpDrv_Slot_UpdateFlag_Complete) && wimpdrv_get_pid(va_get_globals(va_s0), i) !=
    WS_PartitionID(PID_INVALID) ==>
    !(is_mem_region_overlap(wimpdrv_do_get_paddr_base(va_get_globals(va_s0), i),
    wimpdrv_do_get_paddr_end(va_get_globals(va_s0), i), new_do_pbase, new_do_pend)))
  requires var new_wimpdrv_idword:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    var new_do_pbase:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); var new_do_pend:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); wimpdrv_registration_info_must_exist(va_s0.subjects,
    va_s0.objects, va_s0.id_mappings, va_s0.objs_addrs, new_wimpdrv_idword, new_do_pbase,
    new_do_pend)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var drv_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 * ARCH_WORD_BYTES);
    var new_do_pbase:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); var new_do_pend:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 3 * ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP,
    va_s0)); var drv_slot:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) +
    ARCH_WORD_BYTES); ((((((ret == TRUE ==> wimpdrv_valid_slot_id(drv_slot)) && (ret == TRUE ==>
    (forall i:word :: wimpdrv_valid_slot_id(i) ==> wimpdrv_get_id_word(va_get_globals(va_s0), i) !=
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
  reveal_va_code__wimpdrv_activate_private();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EBX),
    va_op_reg_reg(ECX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b7, va_s7, va_sM, va_op_reg_reg(EDX));
  ghost var orig_ebp := va_get_reg(EBP, va_s8);
  ghost var orig_esp := va_get_reg(ESP, va_s8);
  ghost var va_b11, va_s11 := va_lemma_PUSH_VOID(va_b8, va_s8, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(EDX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_PUSH(va_b12, va_s12, va_sM, va_op_word_reg(EDX));
  ghost var va_b14, va_s14 := va_lemma__wimpdrv_find_slot_by_id(va_b13, va_s13, va_sM);
  ghost var va_b15, va_s15 := va_lemma_Load(va_b14, va_s14, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0);
  ghost var va_b16, va_s16 := va_lemma_POP_VOID(va_b15, va_s15, va_sM, 2 * ARCH_WORD_BYTES);
  ghost var va_s17, va_c17, va_b17 := va_lemma_block(va_b16, va_s16, va_sM);
  ghost var va_cond_c17, va_s18:va_state := va_lemma_ifElse(va_get_ifCond(va_c17),
    va_get_ifTrue(va_c17), va_get_ifFalse(va_c17), va_s16, va_s17);
  if (va_cond_c17)
  {
    ghost var va_b19 := va_get_block(va_get_ifTrue(va_c17));
    ghost var va_b20, va_s20 := va_lemma_PUSH_VOID(va_b19, va_s18, va_s17, 1 * ARCH_WORD_BYTES);
    ghost var va_b21, va_s21 := va_lemma_PUSH(va_b20, va_s20, va_s17,
      va_const_word(WimpDrv_ID_RESERVED_EMPTY));
    ghost var va_b22, va_s22 := va_lemma__wimpdrv_find_slot_by_id(va_b21, va_s21, va_s17);
    ghost var va_b23, va_s23 := va_lemma_Load(va_b22, va_s22, va_s17, va_op_word_reg(ECX),
      va_op_word_reg(ESP), 0);
    ghost var va_b24, va_s24 := va_lemma_Load(va_b23, va_s23, va_s17, va_op_word_reg(EBX),
      va_op_word_reg(ESP), ARCH_WORD_BYTES);
    ghost var va_b25, va_s25 := va_lemma_POP_VOID(va_b24, va_s24, va_s17, 2 * ARCH_WORD_BYTES);
    assert va_s25.id_mappings == va_old_s.id_mappings;  // line 333 column 9 of file .\drv/drv_ops_impl.vad
    ghost var va_s27, va_c27, va_b27 := va_lemma_block(va_b25, va_s25, va_s17);
    ghost var va_cond_c27, va_s28:va_state := va_lemma_ifElse(va_get_ifCond(va_c27),
      va_get_ifTrue(va_c27), va_get_ifFalse(va_c27), va_s25, va_s27);
    if (va_cond_c27)
    {
      ghost var va_b29 := va_get_block(va_get_ifTrue(va_c27));
      Lemma__wimpdrv_find_slot_Prove_usbtds_verifiedtds_do_not_associate_wimpdrv(va_get_globals(va_s28),
        va_get_reg(EBX, va_s28));
      assert usbtds_verifiedtds_do_not_associate_wimpdrv(va_get_globals(va_s28), va_get_reg(EBX,
        va_s28));  // line 338 column 13 of file .\drv/drv_ops_impl.vad
      assert va_get_reg(ESP, va_s28) == orig_esp;  // line 339 column 13 of file .\drv/drv_ops_impl.vad
      assert va_get_reg(EBP, va_s28) == orig_ebp;  // line 340 column 13 of file .\drv/drv_ops_impl.vad
      ghost var va_b34, va_s34 := va_lemma_Load(va_b29, va_s28, va_s27, va_op_word_reg(EDX),
        va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
      ghost var va_b35, va_s35 := va_lemma_PUSH(va_b34, va_s34, va_s27, va_op_word_reg(EDX));
      ghost var va_b36, va_s36 := va_lemma_Load(va_b35, va_s35, va_s27, va_op_word_reg(EDX),
        va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
      ghost var va_b37, va_s37 := va_lemma_PUSH(va_b36, va_s36, va_s27, va_op_word_reg(EDX));
      ghost var va_b38, va_s38 := va_lemma_Load(va_b37, va_s37, va_s27, va_op_word_reg(EDX),
        va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
      ghost var va_b39, va_s39 := va_lemma_PUSH(va_b38, va_s38, va_s27, va_op_word_reg(EDX));
      ghost var va_b40, va_s40 := va_lemma_Load(va_b39, va_s39, va_s27, va_op_word_reg(EDX),
        va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
      ghost var va_b41, va_s41 := va_lemma_PUSH(va_b40, va_s40, va_s27, va_op_word_reg(EDX));
      ghost var in_drv_id := va_get_reg(EDX, va_s41);
      ghost var va_b43, va_s43 := va_lemma_PUSH(va_b41, va_s41, va_s27, va_op_word_reg(EBX));
      ghost var va_b44, va_s44 := va_lemma__wimpdrv_update_slot_pid_to_valid(va_b43, va_s43,
        va_s27);
      assert WimpDrv_IDWord_ToDrvID(va_s44.subjects, va_s44.objects, va_s44.id_mappings, in_drv_id)
        in va_s44.subjects.wimp_drvs;  // line 354 column 13 of file .\drv/drv_ops_impl.vad
      assert va_get_reg(ESP, va_s44) == orig_esp - 5 * ARCH_WORD_BYTES;  // line 355 column 13 of file .\drv/drv_ops_impl.vad
      ghost var va_b47, va_s47 := va_lemma_POP_VOID(va_b44, va_s44, va_s27, 5 * ARCH_WORD_BYTES);
      ghost var va_b48, va_s48 := va_lemma_PUSH_Reg1ToReg6(va_b47, va_s47, va_s27);
      ghost var va_b49, va_s49 := va_lemma_PUSH(va_b48, va_s48, va_s27, va_op_word_reg(EBX));
      ghost var va_b50, va_s50 := va_lemma_CALL_WimpDrv_DO_Clear(va_b49, va_s49, va_s27);
      assert va_get_reg(ESP, va_s50) == orig_esp - 7 * ARCH_WORD_BYTES;  // line 362 column 13 of file .\drv/drv_ops_impl.vad
      ghost var va_b52, va_s52 := va_lemma_POP_VOID(va_b50, va_s50, va_s27, 1 * ARCH_WORD_BYTES);
      ghost var va_b53, va_s53 := va_lemma_POP_Reg1ToReg6(va_b52, va_s52, va_s27);
      assert va_get_reg(EBP, va_s53) == orig_ebp;  // line 367 column 13 of file .\drv/drv_ops_impl.vad
      ghost var va_b55, va_s55 := va_lemma_Store(va_b53, va_s53, va_s27, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      ghost var va_b56, va_s56 := va_lemma_Store(va_b55, va_s55, va_s27, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_op_word_reg(EBX));
      va_s27 := va_lemma_empty(va_s56, va_s27);
    }
    else
    {
      ghost var va_b57 := va_get_block(va_get_ifFalse(va_c27));
      assert va_get_reg(EBP, va_s28) == orig_ebp;  // line 373 column 13 of file .\drv/drv_ops_impl.vad
      ghost var va_b59, va_s59 := va_lemma_Store(va_b57, va_s28, va_s27, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s59, va_s27, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY));
      assert va_get_globals(va_s60) == va_get_globals(va_old_s);  // line 377 column 13 of file .\drv/drv_ops_impl.vad
      Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
        va_get_globals(va_s60));
      va_s27 := va_lemma_empty(va_s60, va_s27);
    }
    va_s17 := va_lemma_empty(va_s27, va_s17);
  }
  else
  {
    ghost var va_b63 := va_get_block(va_get_ifFalse(va_c17));
    assert va_get_reg(EBP, va_s18) == orig_ebp;  // line 383 column 9 of file .\drv/drv_ops_impl.vad
    ghost var va_b65, va_s65 := va_lemma_Store(va_b63, va_s18, va_s17, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b66, va_s66 := va_lemma_Store(va_b65, va_s65, va_s17, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(WimpDrv_SlotID_EMPTY));
    assert va_get_globals(va_s66) == va_get_globals(va_old_s);  // line 387 column 9 of file .\drv/drv_ops_impl.vad
    Lemma_global_non_scratchpad_vars_are_unchanged_ProveIfGlobalVarsAreEqual(va_get_globals(va_old_s),
      va_get_globals(va_s66));
    va_s17 := va_lemma_empty(va_s66, va_s17);
  }
  ghost var va_b69, va_s69 := va_lemma_POP_OneReg(va_b17, va_s17, va_sM, va_op_reg_reg(EDX));
  ghost var va_b70, va_s70 := va_lemma_POP_TwoRegs(va_b69, va_s69, va_sM, va_op_reg_reg(EBX),
    va_op_reg_reg(ECX));
  ghost var va_b71, va_s71 := va_lemma_POP_OneReg(va_b70, va_s70, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s71, va_sM);
}
//--
lemma Lemma_usbtds_verifiedtds_do_not_associate_wimpdrv_HoldIfUSBTDsAreUnchanged(
    globals1:globalsmap, globals2:globalsmap, wimpdrv_slot:uint32
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires wimpdrv_valid_slot_id(wimpdrv_slot)

    requires usbtds_verifiedtds_do_not_associate_wimpdrv(globals1, wimpdrv_slot)
    requires global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM())
    
    ensures usbtds_verifiedtds_do_not_associate_wimpdrv(globals2, wimpdrv_slot)
{
    reveal usbtds_verifiedtds_do_not_associate_wimpdrv();
}

// Lemma: In <WimpDrv_Deactivate>, prove all wimp DOs overlap with the physical memory region [do_pbase, do_pend) is inactive
lemma Lemma_WimpDrv_Deactivate_ProveNoActiveWimpDrvOverlapWithDeactivatedPMemRegion(s:state, s':state, wimpdrv_slot_id:word, do_pbase:word, do_pend:uint)
    requires ValidState(s)
    requires ValidState(s')
    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires s.subjects == s'.subjects
    requires s.objects == s'.objects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs

    requires wimpdrv_valid_slot_id(wimpdrv_slot_id)
    requires wimpdrv_get_pid(wkm_get_globals(s.wk_mstate), wimpdrv_slot_id) != WS_PartitionID(PID_INVALID)
    requires wimpdrv_do_get_flag(wkm_get_globals(s.wk_mstate), wimpdrv_slot_id) == WimpDrv_Slot_UpdateFlag_Complete
    requires wimpdrv_do_get_paddr_base(wkm_get_globals(s.wk_mstate), wimpdrv_slot_id) == do_pbase
    requires wimpdrv_do_get_paddr_end(wkm_get_globals(s.wk_mstate), wimpdrv_slot_id) == do_pend

    requires wimpdrv_get_pid(wkm_get_globals(s'.wk_mstate), wimpdrv_slot_id) == WS_PartitionID(PID_INVALID)

    requires WK_ValidPMemRegion(do_pbase, do_pend)

    requires forall i :: wimpdrv_valid_slot_id(i) && i != wimpdrv_slot_id
                ==> p_wimpdrv_slot_equal(wkm_get_globals(s.wk_mstate), wkm_get_globals(s'.wk_mstate), i)
        // Requirement: Other wimp driver slots are unmodified
    
    ensures forall wimpdrv_do_id, pmem :: WSM_IsWimpDrvDOID(s'.objects, wimpdrv_do_id) && 
                pmem in s'.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs
            ==> pmem.paddr_start <= pmem.paddr_end
    ensures forall wimpdrv_do_id, pmem :: WSM_IsWimpDrvDOID(s'.objects, wimpdrv_do_id) && 
                pmem in s'.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs &&
                is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, do_pbase, do_pend)
            ==> WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), wimpdrv_do_id.oid) == WS_PartitionID(PID_INVALID)
        // Property: All wimp DOs overlap with the physical memory region [do_pbase, do_pend) is inactive
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();
    reveal p_wimpdrv_slot_equal();

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var subjs' := s'.subjects;
    var objs' := s'.objects;
    var id_mappings' := s'.id_mappings;
    var objs_addrs' := s'.objs_addrs;
    var globals' := wkm_get_globals(s'.wk_mstate);

    forall wimpdrv_do_id, pmem | WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && 
                pmem in s'.objs_addrs.dos_addrs[wimpdrv_do_id].paddrs &&
                is_mem_region_overlap(pmem.paddr_start, pmem.paddr_end, do_pbase, do_pend)
        ensures WSM_ObjPID(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) == WS_PartitionID(PID_INVALID)
    {
        var obj_pid := WSM_ObjPID(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);

        if(obj_pid != WS_PartitionID(PID_INVALID))
        {
            var cur_wimpdrv_id:Drv_ID := WimpDrvDO_FindOwner(subjs', objs', wimpdrv_do_id.oid);
            Lemma_ObjPID_SamePIDWithOwnerSubject(subjs', objs', id_mappings', globals', cur_wimpdrv_id.sid, wimpdrv_do_id.oid);

            assert WSM_SubjPID(subjs', objs', id_mappings', globals', cur_wimpdrv_id.sid) == obj_pid;
            assert SubjPID_WimpDrv_ByDrvID(subjs', objs', id_mappings', globals', cur_wimpdrv_id) != WS_PartitionID(PID_INVALID);
            var cur_wimpdrv_id_word := WimpDrv_DrvID_ToIDWord(subjs', objs', id_mappings', cur_wimpdrv_id);
            var cur_wimpdrv_slot := wimpdrv_get_slot_by_idword(globals', cur_wimpdrv_id_word);

            assert wimpdrv_do_get_flag(globals', cur_wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete;

            // Prove cur_wimpdrv_slot == wimpdrv_slot_id
            if(cur_wimpdrv_slot != wimpdrv_slot_id)
            {
                // Prove SubjPID_WimpDrv_ByDrvID(subjs, objs, id_mappings, globals, cur_wimpdrv_id) != WS_PartitionID(PID_INVALID);
                assert p_wimpdrv_slot_equal(globals, globals', cur_wimpdrv_slot);
                assert wimpdrv_get_id_word(globals', cur_wimpdrv_slot) == cur_wimpdrv_id_word;
                assert wimpdrv_get_id_word(globals, cur_wimpdrv_slot) == cur_wimpdrv_id_word;
                assert wimpdrv_idword_in_record(globals, cur_wimpdrv_id_word) == wimpdrv_idword_in_record(globals', cur_wimpdrv_id_word);
                assert SubjPID_WimpDrv_ByDrvID(subjs, objs, id_mappings, globals, cur_wimpdrv_id) != WS_PartitionID(PID_INVALID);

                assert wimpdrv_get_pid(globals, wimpdrv_slot_id) != WS_PartitionID(PID_INVALID);
                assert wimpdrv_do_get_flag(globals, wimpdrv_slot_id) == WimpDrv_Slot_UpdateFlag_Complete;

                // Prove !WK_WimpDrv_DOMustNotOverlapWithEachOther(globals, cur_wimpdrv_slot, wimpdrv_slot_id);
                var cur_do_paddr_base := wimpdrv_do_get_paddr_base(globals, cur_wimpdrv_slot);
                var cur_do_paddr_end := wimpdrv_do_get_paddr_end(globals, cur_wimpdrv_slot);
                var do_paddr_base := wimpdrv_do_get_paddr_base(globals, wimpdrv_slot_id);
                var do_paddr_end := wimpdrv_do_get_paddr_end(globals, wimpdrv_slot_id);

                assert wimpdrv_get_pid(globals, cur_wimpdrv_slot) != WS_PartitionID(PID_INVALID);
                assert wimpdrv_get_pid(globals, wimpdrv_slot_id) != WS_PartitionID(PID_INVALID);
                assert wimpdrv_do_get_flag(globals, cur_wimpdrv_slot) == WimpDrv_Slot_UpdateFlag_Complete;
                assert wimpdrv_do_get_flag(globals, wimpdrv_slot_id) == WimpDrv_Slot_UpdateFlag_Complete;

                Lemma_WimpDrv_DORegionMatchInfoInObjsAddrs(subjs', objs', id_mappings', objs_addrs', globals', cur_wimpdrv_slot);
                assert cur_do_paddr_base == pmem.paddr_start;
                assert cur_do_paddr_end == pmem.paddr_end;
                assert do_pbase == do_paddr_base;
                assert do_pend == do_paddr_end;
                assert is_mem_region_overlap(cur_do_paddr_base, cur_do_paddr_end, do_paddr_base, do_paddr_end);

                assert !WK_WimpDrv_DOMustNotOverlapWithEachOther(globals, cur_wimpdrv_slot, wimpdrv_slot_id);

                assert false;
            }
            assert cur_wimpdrv_slot == wimpdrv_slot_id;

            assert false;
        }
    }
}
