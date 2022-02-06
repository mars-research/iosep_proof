include "ins/x86/ins_wrapper.gen.dfy"
include "wk_ops_commons.dfy"
include "partition_id.s.dfy"
include "dev\\usb2\\eehci_info.i.dfy"
include "dev\\usb2\\usb_tds.i.dfy"
include "dev\\usb2\\usb_pdev.i.dfy"
include "drv\\public\\wimpdrv_lemmas.i.dfy"
include "drv\\drv.i.dfy"
//-- pid_generate

function method{:opaque} va_code_pid_generate(ret:va_operand_reg):va_code
{
  va_Block(va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDI), G_PID_Counter()),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_PID_Counter(), va_op_reg_reg(EDI),
    va_const_word(0)), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_const_cmp(PID_MAX)),
    va_Block(va_CCons(va_code_MOV_ToReg(ret, va_const_word(PID_GENERATE_FUNC_ERROR)), va_CNil())),
    va_Block(va_CCons(va_code_ADD(va_op_word_reg(ESI), va_const_word(1)),
    va_CCons(va_code_STRglobal(G_PID_Counter(), va_op_reg_reg(EDI), va_const_word(0),
    va_op_word_reg(ESI)), va_CCons(va_code_MOV_ToReg(ret, va_op_word_reg(ESI)), va_CNil()))))),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)), va_CNil()))))))
}

lemma va_lemma_pid_generate(va_b0:va_codes, va_s0:va_state, va_sN:va_state, ret:va_operand_reg)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_pid_generate(ret), va_s0, va_sN)
  requires va_is_dst_reg(ret, va_s0)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires ret == Reg1
  requires IsAddrInStack(va_get_reg(ESP, va_s0) - 2 * ARCH_WORD_BYTES)
  requires gvar_read_word_byoffset(va_s0.wk_mstate, G_PID_Counter(), 0) !=
    PID_RESERVED_OS_PARTITION - 1
  requires PID_INVALID == 0
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  globals_other_gvar_unchanged(va_get_globals(va_s0), va_get_globals(va_sM),
    G_PID_Counter())
  ensures  va_eval_reg(va_sM, ret) != PID_INVALID
  ensures  va_eval_reg(va_sM, ret) != PID_GENERATE_FUNC_ERROR ==>
    !(WS_PartitionID(va_eval_reg(va_sM, ret)) in pids_parse_g_wimp_pids(va_get_globals(va_sM)))
  ensures  va_eval_reg(va_sM, ret) != PID_GENERATE_FUNC_ERROR ==> (forall pid:WS_PartitionID :: pid
    in pids_parse_g_wimp_pids(va_get_globals(va_sM)) ==> pid.v != va_eval_reg(va_sM, ret))
  ensures  va_eval_reg(va_sM, ret) != PID_GENERATE_FUNC_ERROR ==> va_eval_reg(va_sM, ret) <=
    pids_parse_g_pid_counter(va_get_globals(va_sM)).v
  ensures  va_eval_reg(va_sM, ret) == PID_GENERATE_FUNC_ERROR ==> va_get_globals(va_sM) ==
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
  reveal_va_code_pid_generate();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b4, va_s4 := va_lemma_PUSH_TwoRegs(va_b1, va_s0, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b5, va_s5 := va_lemma_LDRglobaladdr_ToReg(va_b4, va_s4, va_sM, va_op_reg_reg(EDI),
    G_PID_Counter());
  ghost var va_b6, va_s6 := va_lemma_LDRglobal(va_b5, va_s5, va_sM, va_op_word_reg(ESI),
    G_PID_Counter(), va_op_reg_reg(EDI), va_const_word(0));
  ghost var va_s7, va_c7, va_b7 := va_lemma_block(va_b6, va_s6, va_sM);
  ghost var va_cond_c7, va_s8:va_state := va_lemma_ifElse(va_get_ifCond(va_c7),
    va_get_ifTrue(va_c7), va_get_ifFalse(va_c7), va_s6, va_s7);
  if (va_cond_c7)
  {
    ghost var va_b9 := va_get_block(va_get_ifTrue(va_c7));
    ghost var va_b10, va_s10 := va_lemma_MOV_ToReg(va_b9, va_s8, va_s7, ret,
      va_const_word(PID_GENERATE_FUNC_ERROR));
    va_s7 := va_lemma_empty(va_s10, va_s7);
  }
  else
  {
    ghost var va_b11 := va_get_block(va_get_ifFalse(va_c7));
    ghost var va_b12, va_s12 := va_lemma_ADD(va_b11, va_s8, va_s7, va_op_word_reg(ESI),
      va_const_word(1));
    ghost var new_globals := global_write_word(va_get_globals(va_s12), G_PID_Counter(),
      va_get_reg(EDI, va_s12), va_get_reg(ESI, va_s12));
    ghost var new_this := va_s12.(wk_mstate := va_s12.wk_mstate.(globals := new_globals));
    Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s12),
      new_globals);
    Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(va_get_globals(va_s12),
      new_globals);
    assert global_read_fullval(new_globals, G_WimpDrvs_Info()) ==
      global_read_fullval(va_get_globals(va_s12), G_WimpDrvs_Info());  // line 79 column 9 of file .\partition_id_ops.vad
    Lemma_WK_WimpDrvs_ValidGlobalVarValues_IDWords_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s12),
      new_globals);
    Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s12),
      new_globals);
    Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s12),
      new_globals);
    Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfGExistingPIDsAndEECHIInfoUnchanged(va_get_globals(va_s12),
      new_globals);
    Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(va_get_globals(va_s12),
      new_globals);
    Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(va_get_globals(va_s12),
      new_globals);
    Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s12),
      new_globals);
    Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s12,
      new_this);
    Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s12,
      new_this);
    assert ins_valid_strglobal_word(va_s12.subjects, va_s12.objects, va_s12.id_mappings,
      va_s12.objs_addrs, va_s12.activate_conds, va_get_globals(va_s12), G_PID_Counter(),
      va_get_reg(EDI, va_s12), va_get_reg(ESI, va_s12));  // line 91 column 9 of file .\partition_id_ops.vad
    ghost var va_b28, va_s28 := va_lemma_STRglobal(va_b12, va_s12, va_s7, G_PID_Counter(),
      va_op_reg_reg(EDI), va_const_word(0), va_op_word_reg(ESI));
    Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(va_get_globals(va_old_s),
      va_get_globals(va_s28));
    Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
      va_s28);
    ghost var va_b31, va_s31 := va_lemma_MOV_ToReg(va_b28, va_s28, va_s7, ret, va_op_word_reg(ESI));
    va_s7 := va_lemma_empty(va_s31, va_s7);
  }
  ghost var va_b32, va_s32 := va_lemma_POP_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  va_sM := va_lemma_empty(va_s32, va_sM);
}
//--
//-- pid_existing_read_pid

function method{:opaque} va_code_pid_existing_read_pid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EDX), G_Existing_PIDs()),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WK_Existing_PID_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_Existing_PIDs_Entry_PID_BytesOffset)),
    va_CCons(va_code_LDRglobal(va_op_word_reg(ESI), G_Existing_PIDs(), va_op_reg_reg(EDX),
    va_op_word_reg(EDI)), va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(EDI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))
}

lemma va_lemma_pid_existing_read_pid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_pid_existing_read_pid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    pids_valid_slot(slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var in_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    out_pid:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); out_pid ==
    pids_get_pid(va_get_globals(va_sM), in_slot).v
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
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_pid_existing_read_pid();
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
    G_Existing_PIDs());
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s10);
  Lemma_NatMul_Ineq_4var(slot, WK_Existing_PID_ENTRY_SZ, WK_Existing_PIDs_ENTRIES,
    WK_Existing_PID_ENTRY_SZ);
  assert isUInt32(slot * WK_Existing_PID_ENTRY_SZ);  // line 163 column 5 of file .\partition_id_ops.vad
  ghost var va_b14, va_s14 := va_lemma_MUL_Reg_32BitsResult(va_b10, va_s10, va_sM,
    va_op_reg_reg(EDI), va_const_word(WK_Existing_PID_ENTRY_SZ));
  ghost var va_b15, va_s15 := va_lemma_ADD(va_b14, va_s14, va_sM, va_op_word_reg(EDI),
    va_const_word(G_Existing_PIDs_Entry_PID_BytesOffset));
  ghost var va_b16, va_s16 := va_lemma_LDRglobal(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    G_Existing_PIDs(), va_op_reg_reg(EDX), va_op_word_reg(EDI));
  ghost var va_b17, va_s17 := va_lemma_Store(va_b16, va_s16, va_sM, va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_op_word_reg(ESI));
  ghost var va_b18, va_s18 := va_lemma_POP_OneReg(va_b17, va_s17, va_sM, va_op_reg_reg(ESI));
  ghost var va_b19, va_s19 := va_lemma_POP_TwoRegs(va_b18, va_s18, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(EDI));
  ghost var va_b20, va_s20 := va_lemma_POP_OneReg(va_b19, va_s19, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s20, va_sM);
}
//--
//-- pid_existing_write_pid

function method{:opaque} va_code_pid_existing_write_pid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EBX), G_Existing_PIDs()),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WK_Existing_PID_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_Existing_PIDs_Entry_PID_BytesOffset)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_op_word_reg(EBX)),
    va_CCons(va_code_ADD(va_op_word_reg(ECX), va_op_word_reg(EDI)),
    va_CCons(va_code_STRglobal(G_Existing_PIDs(), va_op_reg_reg(ECX), va_const_word(0),
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))
}

lemma va_lemma_pid_existing_write_pid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_pid_existing_write_pid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    ((pids_valid_slot(slot) && !(pids_is_os_pid(new_pid))) && new_pid <=
    pids_parse_g_pid_counter(va_get_globals(va_s0)).v) && (forall pid:WS_PartitionID :: pid in
    pids_parse_g_wimp_pids(va_get_globals(va_s0)) ==> pid.v != new_pid)
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var
    old_pid := pids_get_pid(va_get_globals(va_s0), slot); (((forall i:int :: 0 <= i <
    WimpDrv_Info_ENTRIES ==> wimpdrv_get_pid(va_get_globals(va_s0), i) ==
    WS_PartitionID(PID_INVALID) || wimpdrv_get_pid(va_get_globals(va_s0), i) != old_pid) && (forall
    i:int :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_pid(va_get_globals(va_s0), i) ==
    WS_PartitionID(PID_INVALID) || usbtd_map_get_pid(va_get_globals(va_s0), i) != old_pid)) &&
    (forall i:int :: 0 <= i < eEHCI_INSTANCE_NUM ==> eehci_info_get_pid(va_get_globals(va_s0), i)
    == WS_PartitionID(PID_INVALID) || eehci_info_get_pid(va_get_globals(va_s0), i) != old_pid)) &&
    (forall i:int :: 0 <= i < WimpUSBPDev_Info_ENTRIES ==> usbpdev_get_pid(va_get_globals(va_s0),
    i) == WS_PartitionID(PID_INVALID) || usbpdev_get_pid(va_get_globals(va_s0), i) != old_pid)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    new_pid == pids_get_pid(va_get_globals(va_sM), slot).v &&
    pid_existing_updateslot_update_one_slot_only(va_get_globals(va_s0), va_get_globals(va_sM), slot)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 0 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_pid_existing_write_pid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBX));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b10, va_s10 := va_lemma_PUSH_OneReg(va_b9, va_s9, va_sM, va_op_reg_reg(ECX));
  ghost var va_b11, va_s11 := va_lemma_LDRglobaladdr_ToReg(va_b10, va_s10, va_sM,
    va_op_reg_reg(EBX), G_Existing_PIDs());
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s13);
  Lemma_NatMul_Ineq_4var(slot, WK_Existing_PID_ENTRY_SZ, WK_Existing_PIDs_ENTRIES,
    WK_Existing_PID_ENTRY_SZ);
  assert isUInt32(slot * WK_Existing_PID_ENTRY_SZ);  // line 270 column 5 of file .\partition_id_ops.vad
  ghost var va_b17, va_s17 := va_lemma_MUL_Reg_32BitsResult(va_b13, va_s13, va_sM,
    va_op_reg_reg(EDI), va_const_word(WK_Existing_PID_ENTRY_SZ));
  ghost var va_b18, va_s18 := va_lemma_ADD(va_b17, va_s17, va_sM, va_op_word_reg(EDI),
    va_const_word(G_Existing_PIDs_Entry_PID_BytesOffset));
  ghost var va_b19, va_s19 := va_lemma_MOV_ToReg(va_b18, va_s18, va_sM, va_op_reg_reg(ECX),
    va_op_word_reg(EBX));
  ghost var va_b20, va_s20 := va_lemma_ADD(va_b19, va_s19, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EDI));
  ghost var old_pid := global_read_word(va_get_globals(va_s20), G_Existing_PIDs(), va_get_reg(ECX,
    va_s20));
  ghost var new_globals := global_write_word(va_get_globals(va_s20), G_Existing_PIDs(),
    va_get_reg(ECX, va_s20), va_get_reg(ESI, va_s20));
  ghost var new_this := va_s20.(wk_mstate := va_s20.wk_mstate.(globals := new_globals));
  Lemma_pids_g_existing_pids_no_duplicate_HoldAfterWritingNonDuplicateValue(va_get_globals(va_s20),
    new_globals, va_get_reg(ECX, va_s20), va_get_reg(ESI, va_s20));
  assert global_read_fullval(new_globals, G_WimpDrvs_Info()) ==
    global_read_fullval(va_get_globals(va_s20), G_WimpDrvs_Info());  // line 284 column 5 of file .\partition_id_ops.vad
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfOverwritePIDOfPartitionHavingNoWimpDrvs(va_get_globals(va_s20),
    new_globals, va_get_reg(ECX, va_s20), old_pid, va_get_reg(ESI, va_s20));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s20),
    new_globals);
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfOverwritePIDOfPartitionHavingNoWimpDrvs(va_get_globals(va_s20),
    new_globals, va_get_reg(ECX, va_s20), old_pid, va_get_reg(ESI, va_s20));
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_IfGWimpPDevInfoUnchanged(va_get_globals(va_s20),
    new_globals);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfNotWritingInOSPID(va_get_globals(va_s20),
    new_globals, va_get_reg(ECX, va_s20), va_get_reg(ESI, va_s20));
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfOverwritePIDOfPartitionHavingNoEEHCI(va_get_globals(va_s20),
    new_globals, va_get_reg(ECX, va_s20), old_pid, va_get_reg(ESI, va_s20));
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfOverwritePIDOfPartitionHavingNoUSBTD(va_get_globals(va_s20),
    new_globals, va_get_reg(ECX, va_s20), old_pid, va_get_reg(ESI, va_s20));
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s20),
    new_globals);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s20,
    new_this);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s20,
    new_this);
  assert ins_valid_strglobal_word(va_s20.subjects, va_s20.objects, va_s20.id_mappings,
    va_s20.objs_addrs, va_s20.activate_conds, va_get_globals(va_s20), G_Existing_PIDs(),
    va_get_reg(ECX, va_s20), va_get_reg(ESI, va_s20));  // line 302 column 5 of file .\partition_id_ops.vad
  ghost var va_b37, va_s37 := va_lemma_STRglobal(va_b20, va_s20, va_sM, G_Existing_PIDs(),
    va_op_reg_reg(ECX), va_const_word(0), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_s37));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s37);
  ghost var va_b40, va_s40 := va_lemma_POP_OneReg(va_b37, va_s37, va_sM, va_op_reg_reg(ECX));
  ghost var va_b41, va_s41 := va_lemma_POP_TwoRegs(va_b40, va_s40, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b42, va_s42 := va_lemma_POP_OneReg(va_b41, va_s41, va_sM, va_op_reg_reg(EBX));
  ghost var va_b43, va_s43 := va_lemma_POP_OneReg(va_b42, va_s42, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s43, va_sM);
}
//--
//-- pid_existing_write_pid_invalid

function method{:opaque} va_code_pid_existing_write_pid_invalid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(ECX)),
    va_CCons(va_code_LDRglobaladdr_ToReg(va_op_reg_reg(EBX), G_Existing_PIDs()),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES),
    va_CCons(va_code_Load(va_op_word_reg(EDI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MUL_Reg_32BitsResult(va_op_reg_reg(EDI),
    va_const_word(WK_Existing_PID_ENTRY_SZ)), va_CCons(va_code_ADD(va_op_word_reg(EDI),
    va_const_word(G_Existing_PIDs_Entry_PID_BytesOffset)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(ECX), va_op_word_reg(EBX)),
    va_CCons(va_code_ADD(va_op_word_reg(ECX), va_op_word_reg(EDI)),
    va_CCons(va_code_STRglobal(G_Existing_PIDs(), va_op_reg_reg(ECX), va_const_word(0),
    va_op_word_reg(ESI)), va_CCons(va_code_POP_OneReg(va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDI), va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))
}

lemma va_lemma_pid_existing_write_pid_invalid(va_b0:va_codes, va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_pid_existing_write_pid_invalid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES);
    pids_valid_slot(slot) && new_pid == PID_INVALID
  requires var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var
    old_pid := pids_get_pid(va_get_globals(va_s0), slot); (((forall i:int :: 0 <= i <
    WimpDrv_Info_ENTRIES ==> wimpdrv_get_pid(va_get_globals(va_s0), i) ==
    WS_PartitionID(PID_INVALID) || wimpdrv_get_pid(va_get_globals(va_s0), i) != old_pid) && (forall
    i:int :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_map_get_pid(va_get_globals(va_s0), i) ==
    WS_PartitionID(PID_INVALID) || usbtd_map_get_pid(va_get_globals(va_s0), i) != old_pid)) &&
    (forall i:int :: 0 <= i < eEHCI_INSTANCE_NUM ==> eehci_info_get_pid(va_get_globals(va_s0), i)
    == WS_PartitionID(PID_INVALID) || eehci_info_get_pid(va_get_globals(va_s0), i) != old_pid)) &&
    (forall i:int :: 0 <= i < WimpUSBPDev_Info_ENTRIES ==> usbpdev_get_pid(va_get_globals(va_s0),
    i) == WS_PartitionID(PID_INVALID) || usbpdev_get_pid(va_get_globals(va_s0), i) != old_pid)
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); var
    old_pid:word := pids_get_pid(va_get_globals(va_s0), slot).v; (new_pid ==
    pids_get_pid(va_get_globals(va_sM), slot).v &&
    pid_existing_updateslot_update_one_slot_only(va_get_globals(va_s0), va_get_globals(va_sM),
    slot)) && pid_existing_write_pid_invalid_property3(va_get_globals(va_s0),
    va_get_globals(va_sM), old_pid)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 0 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code_pid_existing_write_pid_invalid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBX));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b10, va_s10 := va_lemma_PUSH_OneReg(va_b9, va_s9, va_sM, va_op_reg_reg(ECX));
  ghost var va_b11, va_s11 := va_lemma_LDRglobaladdr_ToReg(va_b10, va_s10, va_sM,
    va_op_reg_reg(EBX), G_Existing_PIDs());
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var slot := va_get_reg(EDI, va_s13);
  Lemma_NatMul_Ineq_4var(slot, WK_Existing_PID_ENTRY_SZ, WK_Existing_PIDs_ENTRIES,
    WK_Existing_PID_ENTRY_SZ);
  assert isUInt32(slot * WK_Existing_PID_ENTRY_SZ);  // line 408 column 5 of file .\partition_id_ops.vad
  ghost var va_b17, va_s17 := va_lemma_MUL_Reg_32BitsResult(va_b13, va_s13, va_sM,
    va_op_reg_reg(EDI), va_const_word(WK_Existing_PID_ENTRY_SZ));
  ghost var va_b18, va_s18 := va_lemma_ADD(va_b17, va_s17, va_sM, va_op_word_reg(EDI),
    va_const_word(G_Existing_PIDs_Entry_PID_BytesOffset));
  ghost var va_b19, va_s19 := va_lemma_MOV_ToReg(va_b18, va_s18, va_sM, va_op_reg_reg(ECX),
    va_op_word_reg(EBX));
  ghost var va_b20, va_s20 := va_lemma_ADD(va_b19, va_s19, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EDI));
  ghost var pid_vaddr := va_get_reg(ECX, va_s20);
  assert va_get_globals(va_s20) == va_get_globals(va_old_s);  // line 418 column 5 of file .\partition_id_ops.vad
  assert va_get_reg(ESI, va_s20) == PID_INVALID;  // line 419 column 5 of file .\partition_id_ops.vad
  ghost var old_pid := global_read_word(va_get_globals(va_s20), G_Existing_PIDs(), va_get_reg(ECX,
    va_s20));
  ghost var new_globals := global_write_word(va_get_globals(va_s20), G_Existing_PIDs(),
    va_get_reg(ECX, va_s20), va_get_reg(ESI, va_s20));
  ghost var new_this := va_s20.(wk_mstate := va_s20.wk_mstate.(globals := new_globals));
  Lemma_pids_g_existing_pids_no_duplicate_HoldAfterWritingNonDuplicateValue(va_get_globals(va_s20),
    new_globals, va_get_reg(ECX, va_s20), va_get_reg(ESI, va_s20));
  assert global_read_fullval(new_globals, G_WimpDrvs_Info()) ==
    global_read_fullval(va_get_globals(va_s20), G_WimpDrvs_Info());  // line 426 column 5 of file .\partition_id_ops.vad
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_PIDs_HoldIfOverwritePIDOfPartitionHavingNoWimpDrvs(va_get_globals(va_s20),
    new_globals, va_get_reg(ECX, va_s20), old_pid, va_get_reg(ESI, va_s20));
  Lemma_WK_WimpDrvs_ValidGlobalVarValues_DOPAddrs_PreserveInNewState_IfGWimpDrvsInfoUnchanged(va_get_globals(va_s20),
    new_globals);
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfOverwritePIDOfPartitionHavingNoWimpDrvs(va_get_globals(va_s20),
    new_globals, va_get_reg(ECX, va_s20), old_pid, va_get_reg(ESI, va_s20));
  Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_IfGWimpPDevInfoUnchanged(va_get_globals(va_s20),
    new_globals);
  Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfNotWritingInOSPID(va_get_globals(va_s20),
    new_globals, va_get_reg(ECX, va_s20), va_get_reg(ESI, va_s20));
  Lemma_WK_EEHCI_INFO_ValidGlobalVarValues_HoldIfOverwritePIDOfPartitionHavingNoEEHCI(va_get_globals(va_s20),
    new_globals, va_get_reg(ECX, va_s20), old_pid, va_get_reg(ESI, va_s20));
  Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfOverwritePIDOfPartitionHavingNoUSBTD(va_get_globals(va_s20),
    new_globals, va_get_reg(ECX, va_s20), old_pid, va_get_reg(ESI, va_s20));
  Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(va_get_globals(va_s20),
    new_globals);
  Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(va_s20,
    new_this);
  Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(va_s20,
    new_this);
  assert ins_valid_strglobal_word(va_s20.subjects, va_s20.objects, va_s20.id_mappings,
    va_s20.objs_addrs, va_s20.activate_conds, va_get_globals(va_s20), G_Existing_PIDs(),
    va_get_reg(ECX, va_s20), va_get_reg(ESI, va_s20));  // line 444 column 5 of file .\partition_id_ops.vad
  ghost var va_b40, va_s40 := va_lemma_STRglobal(va_b20, va_s20, va_sM, G_Existing_PIDs(),
    va_op_reg_reg(ECX), va_const_word(0), va_op_word_reg(ESI));
  Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(va_get_globals(va_old_s),
    va_get_globals(va_s40));
  Lemma_WK_SecureObjsAddrs_MemSeparation_OnWKMStateModification_IfWimpDrvsInfoIsUnchangedAndOSObjsHaveUnchangedPID(va_old_s,
    va_s40);
  Lemma_pids_parse_g_wimp_pids_CorrectnessOfSetChange(va_get_globals(va_old_s),
    va_get_globals(va_s40), pid_vaddr, old_pid, PID_INVALID);
  ghost var va_b44, va_s44 := va_lemma_POP_OneReg(va_b40, va_s40, va_sM, va_op_reg_reg(ECX));
  ghost var va_b45, va_s45 := va_lemma_POP_TwoRegs(va_b44, va_s44, va_sM, va_op_reg_reg(EDI),
    va_op_reg_reg(ESI));
  ghost var va_b46, va_s46 := va_lemma_POP_OneReg(va_b45, va_s45, va_sM, va_op_reg_reg(EBX));
  ghost var va_b47, va_s47 := va_lemma_POP_OneReg(va_b46, va_s46, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s47, va_sM);
}
//--
//-- pid_existing_find_pid_slot

function method{:opaque} va_code_pid_existing_find_pid_slot():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(ESI)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(0)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(TRUE)),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_pid_existing_read_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_While(va_cmp_eq(va_op_cmp_reg(EBX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_pid_existing_read_pid(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_op_cmp_reg(ESI)),
    va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(FALSE)), va_CNil())),
    va_Block(va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EDX), va_const_cmp(WK_Existing_PIDs_ENTRIES
    - 1)), va_Block(va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBX), va_const_word(FALSE)),
    va_CNil())), va_Block(va_CCons(va_code_ADD(va_op_word_reg(EDX), va_const_word(1)),
    va_CNil()))), va_CNil()))), va_CNil()))))))), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX),
    va_op_cmp_reg(ESI)), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(TRUE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_op_word_reg(EDX)), va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 *
    ARCH_WORD_BYTES, va_const_word(PID_SlotID_INVALID)), va_CNil())))),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EDX), va_op_reg_reg(ESI)),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))
}

lemma{:timeLimitMultiplier 5} va_lemma_pid_existing_find_pid_slot(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_pid_existing_find_pid_slot(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var ret:uint32
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var result_slot:uint32 :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); ret == TRUE ==>
    pids_valid_slot(result_slot) && pids_get_pid(va_get_globals(va_sM), result_slot) ==
    WS_PartitionID(pid)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  var stack_retval_space := 2 * ARCH_WORD_BYTES;
    stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM) +
    stack_retval_space)
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_mem(va_sM, va_update_reg(EBP,
    va_sM, va_update_reg(ESP, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDI, va_sM,
    va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_pid_existing_find_pid_slot();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EBX));
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(ESI));
  ghost var begin_state := va_s9;
  ghost var orig_ebp := va_get_reg(EBP, va_s9);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var orig_esi := va_get_reg(ESI, va_s12);
  ghost var va_b14, va_s14 := va_lemma_MOV_ToReg(va_b12, va_s12, va_sM, va_op_reg_reg(EDX),
    va_const_word(0));
  ghost var va_b15, va_s15 := va_lemma_MOV_ToReg(va_b14, va_s14, va_sM, va_op_reg_reg(EBX),
    va_const_word(TRUE));
  ghost var va_b16, va_s16 := va_lemma_PUSH(va_b15, va_s15, va_sM, va_op_word_reg(EDX));
  ghost var va_b17, va_s17 := va_lemma_pid_existing_read_pid(va_b16, va_s16, va_sM);
  ghost var va_b18, va_s18 := va_lemma_Load(va_b17, va_s17, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0);
  ghost var va_b19, va_s19 := va_lemma_POP_VOID(va_b18, va_s18, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_s20, va_c20, va_b20 := va_lemma_block(va_b19, va_s19, va_sM);
  ghost var va_n21:int, va_sW21:va_state := va_lemma_while(va_get_whileCond(va_c20),
    va_get_whileBody(va_c20), va_s19, va_s20);
  while (va_n21 > 0)
    invariant va_whileInv(va_get_whileCond(va_c20), va_get_whileBody(va_c20), va_n21, va_sW21,
      va_s20)
    invariant va_get_ok(va_sW21)
    invariant 0 <= va_get_reg(EDX, va_sW21) <= WK_Existing_PIDs_ENTRIES
    invariant var vaddr1 := AddressOfGlobal(G_Existing_PIDs()) + va_get_reg(EDX, va_sW21) *
      WK_Existing_PID_ENTRY_SZ; (((((((((((va_get_reg(EBX, va_sW21) == TRUE ==>
      is_valid_addr(vaddr1)) && (va_get_reg(EBX, va_sW21) == TRUE ==> is_valid_vaddr(vaddr1))) &&
      (va_get_reg(EBX, va_sW21) == TRUE ==> is_gvar_valid_vaddr(G_Existing_PIDs(), vaddr1))) &&
      (va_get_reg(EBX, va_sW21) != TRUE ==> va_get_reg(EAX, va_sW21) == va_get_reg(ESI, va_sW21) ||
      va_get_reg(EDX, va_sW21) == WK_Existing_PIDs_ENTRIES - 1)) && (va_get_reg(EBX, va_sW21) !=
      TRUE && va_get_reg(EAX, va_sW21) == va_get_reg(ESI, va_sW21) ==> va_get_reg(EDX, va_sW21) <=
      WK_Existing_PIDs_ENTRIES - 1 && gvar_read_word_byaddr(va_sW21.wk_mstate, G_Existing_PIDs(),
      vaddr1) == va_get_reg(ESI, va_sW21))) && va_get_reg(ESP, va_sW21) == va_get_reg(ESP,
      va_old_s) - 5 * ARCH_WORD_BYTES) && stack_under_sp_is_unchanged(begin_state.wk_mstate.m,
      va_sW21.wk_mstate.m, va_get_reg(ESP, va_sW21))) && va_get_reg(ESI, va_sW21) == orig_esi) &&
      va_get_reg(EBP, va_sW21) == orig_ebp) && va_get_reg(EDI, va_sW21) == va_get_reg(EDI,
      va_old_s)) && va_get_reg(ECX, va_sW21) == va_get_reg(ECX, va_old_s)) &&
      state_equal_except_mstate(va_old_s, va_sW21)
    invariant va_state_eq(va_sW21, va_update_reg(EDX, va_sW21, va_update_reg(ECX, va_sW21,
      va_update_reg(EBX, va_sW21, va_update_reg(EAX, va_sW21, va_update_mem(va_sW21,
      va_update_reg(EBP, va_sW21, va_update_reg(ESP, va_sW21, va_update_reg(ESI, va_sW21,
      va_update_reg(EDI, va_sW21, va_update_ok(va_sW21, va_s0)))))))))))
    decreases WK_Existing_PIDs_ENTRIES - va_get_reg(EDX, va_sW21), va_get_reg(EBX, va_sW21)
  {
    ghost var va_s21:va_state, va_sW22:va_state := va_lemma_whileTrue(va_get_whileCond(va_c20),
      va_get_whileBody(va_c20), va_n21, va_sW21, va_s20);
    ghost var va_b23 := va_get_block(va_get_whileBody(va_c20));
    ghost var va_b24, va_s24 := va_lemma_PUSH(va_b23, va_s21, va_sW22, va_op_word_reg(EDX));
    ghost var va_b25, va_s25 := va_lemma_pid_existing_read_pid(va_b24, va_s24, va_sW22);
    ghost var va_b26, va_s26 := va_lemma_Load(va_b25, va_s25, va_sW22, va_op_word_reg(EAX),
      va_op_word_reg(ESP), 0);
    ghost var va_b27, va_s27 := va_lemma_POP_VOID(va_b26, va_s26, va_sW22, 1 * ARCH_WORD_BYTES);
    ghost var va_s28, va_c28, va_b28 := va_lemma_block(va_b27, va_s27, va_sW22);
    ghost var va_cond_c28, va_s29:va_state := va_lemma_ifElse(va_get_ifCond(va_c28),
      va_get_ifTrue(va_c28), va_get_ifFalse(va_c28), va_s27, va_s28);
    if (va_cond_c28)
    {
      ghost var va_b30 := va_get_block(va_get_ifTrue(va_c28));
      ghost var va_b31, va_s31 := va_lemma_MOV_ToReg(va_b30, va_s29, va_s28, va_op_reg_reg(EBX),
        va_const_word(FALSE));
      va_s28 := va_lemma_empty(va_s31, va_s28);
    }
    else
    {
      ghost var va_b32 := va_get_block(va_get_ifFalse(va_c28));
      ghost var va_s33, va_c33, va_b33 := va_lemma_block(va_b32, va_s29, va_s28);
      ghost var va_cond_c33, va_s34:va_state := va_lemma_ifElse(va_get_ifCond(va_c33),
        va_get_ifTrue(va_c33), va_get_ifFalse(va_c33), va_s29, va_s33);
      if (va_cond_c33)
      {
        ghost var va_b35 := va_get_block(va_get_ifTrue(va_c33));
        ghost var va_b36, va_s36 := va_lemma_MOV_ToReg(va_b35, va_s34, va_s33, va_op_reg_reg(EBX),
          va_const_word(FALSE));
        va_s33 := va_lemma_empty(va_s36, va_s33);
      }
      else
      {
        ghost var va_b37 := va_get_block(va_get_ifFalse(va_c33));
        ghost var va_b38, va_s38 := va_lemma_ADD(va_b37, va_s34, va_s33, va_op_word_reg(EDX),
          va_const_word(1));
        va_s33 := va_lemma_empty(va_s38, va_s33);
      }
      va_s28 := va_lemma_empty(va_s33, va_s28);
    }
    va_sW22 := va_lemma_empty(va_s28, va_sW22);
    va_sW21 := va_sW22;
    va_n21 := va_n21 - 1;
  }
  va_s20 := va_lemma_whileFalse(va_get_whileCond(va_c20), va_get_whileBody(va_c20), va_sW21,
    va_s20);
  ghost var va_s39, va_c39, va_b39 := va_lemma_block(va_b20, va_s20, va_sM);
  ghost var va_cond_c39, va_s40:va_state := va_lemma_ifElse(va_get_ifCond(va_c39),
    va_get_ifTrue(va_c39), va_get_ifFalse(va_c39), va_s20, va_s39);
  if (va_cond_c39)
  {
    ghost var va_b41 := va_get_block(va_get_ifTrue(va_c39));
    ghost var va_b42, va_s42 := va_lemma_Store(va_b41, va_s40, va_s39, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    ghost var va_b43, va_s43 := va_lemma_Store(va_b42, va_s42, va_s39, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_op_word_reg(EDX));
    va_s39 := va_lemma_empty(va_s43, va_s39);
  }
  else
  {
    ghost var va_b44 := va_get_block(va_get_ifFalse(va_c39));
    assert va_get_reg(EDX, va_s40) == WK_Existing_PIDs_ENTRIES - 1;  // line 586 column 9 of file .\partition_id_ops.vad
    ghost var va_b46, va_s46 := va_lemma_Store(va_b44, va_s40, va_s39, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b47, va_s47 := va_lemma_Store(va_b46, va_s46, va_s39, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(PID_SlotID_INVALID));
    va_s39 := va_lemma_empty(va_s47, va_s39);
  }
  ghost var va_b48, va_s48 := va_lemma_POP_TwoRegs(va_b39, va_s39, va_sM, va_op_reg_reg(EDX),
    va_op_reg_reg(ESI));
  ghost var va_b49, va_s49 := va_lemma_POP_TwoRegs(va_b48, va_s48, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EBX));
  ghost var va_b50, va_s50 := va_lemma_POP_OneReg(va_b49, va_s49, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s50, va_sM);
}
//--
//-- pids_is_existing_wimp_pid

function method{:opaque} va_code_pids_is_existing_wimp_pid():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EBX), va_op_reg_reg(ECX)),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(EBP), ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EAX), va_const_cmp(PID_INVALID)),
    va_Block(va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EAX)), va_CCons(va_code_pid_existing_find_pid_slot(),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), 0),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), ARCH_WORD_BYTES),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES, va_op_word_reg(EBX)),
    va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(PID_SlotID_INVALID)), va_CNil())))), va_CNil())))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CCons(va_code_Store(va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES,
    va_const_word(PID_SlotID_INVALID)), va_CNil())))),
    va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EBX), va_op_reg_reg(ECX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EAX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))
}

lemma{:timeLimitMultiplier 3} va_lemma_pids_is_existing_wimp_pid(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code_pids_is_existing_wimp_pid(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 4 * ARCH_WORD_BYTES + 13 * ARCH_WORD_BYTES + 2 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_retval_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_retval_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var pid:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var ret:uint32
    := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); var result_slot:uint32 :=
    stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0) + ARCH_WORD_BYTES); (ret == TRUE ==>
    pids_is_existing_wimp_pid(va_get_globals(va_s0), pid)) && (ret == TRUE ==>
    pids_valid_slot(result_slot) && pids_get_pid(va_get_globals(va_s0), result_slot) ==
    WS_PartitionID(pid))
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
  ensures  va_state_eq(va_sM, va_update_reg(EAX, va_sM, va_update_reg(EBX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EDX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code_pids_is_existing_wimp_pid();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b7, va_s7 := va_lemma_PUSH_OneReg(va_b3, va_s3, va_sM, va_op_reg_reg(EAX));
  ghost var va_b8, va_s8 := va_lemma_PUSH_TwoRegs(va_b7, va_s7, va_sM, va_op_reg_reg(EBX),
    va_op_reg_reg(ECX));
  ghost var va_b9, va_s9 := va_lemma_Load(va_b8, va_s8, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(EBP), ARCH_WORD_BYTES);
  ghost var va_s10, va_c10, va_b10 := va_lemma_block(va_b9, va_s9, va_sM);
  ghost var va_cond_c10, va_s11:va_state := va_lemma_ifElse(va_get_ifCond(va_c10),
    va_get_ifTrue(va_c10), va_get_ifFalse(va_c10), va_s9, va_s10);
  if (va_cond_c10)
  {
    ghost var va_b12 := va_get_block(va_get_ifTrue(va_c10));
    ghost var va_b13, va_s13 := va_lemma_PUSH_VOID(va_b12, va_s11, va_s10, 1 * ARCH_WORD_BYTES);
    ghost var va_b14, va_s14 := va_lemma_PUSH(va_b13, va_s13, va_s10, va_op_word_reg(EAX));
    ghost var va_b15, va_s15 := va_lemma_pid_existing_find_pid_slot(va_b14, va_s14, va_s10);
    ghost var va_b16, va_s16 := va_lemma_Load(va_b15, va_s15, va_s10, va_op_word_reg(ECX),
      va_op_word_reg(ESP), 0);
    ghost var va_b17, va_s17 := va_lemma_Load(va_b16, va_s16, va_s10, va_op_word_reg(EBX),
      va_op_word_reg(ESP), ARCH_WORD_BYTES);
    ghost var va_b18, va_s18 := va_lemma_POP_VOID(va_b17, va_s17, va_s10, 2 * ARCH_WORD_BYTES);
    ghost var va_s19, va_c19, va_b19 := va_lemma_block(va_b18, va_s18, va_s10);
    ghost var va_cond_c19, va_s20:va_state := va_lemma_ifElse(va_get_ifCond(va_c19),
      va_get_ifTrue(va_c19), va_get_ifFalse(va_c19), va_s18, va_s19);
    if (va_cond_c19)
    {
      ghost var va_b21 := va_get_block(va_get_ifTrue(va_c19));
      ghost var va_b22, va_s22 := va_lemma_Store(va_b21, va_s20, va_s19, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      ghost var va_b23, va_s23 := va_lemma_Store(va_b22, va_s22, va_s19, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_op_word_reg(EBX));
      va_s19 := va_lemma_empty(va_s23, va_s19);
    }
    else
    {
      ghost var va_b24 := va_get_block(va_get_ifFalse(va_c19));
      ghost var va_b25, va_s25 := va_lemma_Store(va_b24, va_s20, va_s19, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      ghost var va_b26, va_s26 := va_lemma_Store(va_b25, va_s25, va_s19, va_op_word_reg(EBP), 2 *
        ARCH_WORD_BYTES, va_const_word(PID_SlotID_INVALID));
      va_s19 := va_lemma_empty(va_s26, va_s19);
    }
    va_s10 := va_lemma_empty(va_s19, va_s10);
  }
  else
  {
    ghost var va_b27 := va_get_block(va_get_ifFalse(va_c10));
    ghost var va_b28, va_s28 := va_lemma_Store(va_b27, va_s11, va_s10, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    ghost var va_b29, va_s29 := va_lemma_Store(va_b28, va_s28, va_s10, va_op_word_reg(EBP), 2 *
      ARCH_WORD_BYTES, va_const_word(PID_SlotID_INVALID));
    va_s10 := va_lemma_empty(va_s29, va_s10);
  }
  ghost var va_b30, va_s30 := va_lemma_POP_TwoRegs(va_b10, va_s10, va_sM, va_op_reg_reg(EBX),
    va_op_reg_reg(ECX));
  ghost var va_b31, va_s31 := va_lemma_POP_OneReg(va_b30, va_s30, va_sM, va_op_reg_reg(EAX));
  ghost var va_b32, va_s32 := va_lemma_POP_OneReg(va_b31, va_s31, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s32, va_sM);
}
//--
// Predicate: The global variables are modified as expected
predicate pid_existing_write_pid_invalid_property3(globals1:globalsmap, globals2:globalsmap, old_pid:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
{
    pids_parse_g_wimp_pids(globals2) == pids_parse_g_wimp_pids(globals1) - {WS_PartitionID(old_pid)}
}
