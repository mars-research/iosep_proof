include "eehci.s.dfy"
include "eehci_info.gen.dfy"
include "eehci_mem_utils.gen.dfy"
include "usb_tds_utils.gen.dfy"
include "../../partition_id_ops.gen.dfy"
include "../../drv/drv_ops_utils.gen.dfy"
//-- _WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty1
//--
//-- _WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty2
//--
//-- _WimpDrv_Write_eEHCI_USBTDReg_check_new_value

function method{:opaque} va_code__WimpDrv_Write_eEHCI_USBTDReg_check_new_value():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EDX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EAX), va_op_word_reg(EDI)),
    va_CCons(va_code_eehci_info_get_pid(va_op_reg_reg(EAX)),
    va_CCons(va_code_Load(va_op_word_reg(ESI), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDX)),
    va_CCons(va_code__WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty1(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_usbtd_check_td_slot_id(va_op_reg_reg(EDX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDX)),
    va_CCons(va_code__WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty2(),
    va_CCons(va_code_Load(va_op_word_reg(EAX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_usbtd_get_td_pid(),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ESI), va_op_cmp_reg(ECX)),
    va_Block(va_CCons(va_code_PUSH(va_op_word_reg(EDI)), va_CCons(va_code_eehci_mem_read_id(),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EBX)),
    va_CCons(va_code_eechi_id_get_bus_id(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EDX)), va_CCons(va_code_usbtd_get_bus_id(),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EBX), va_op_cmp_reg(ECX)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil())))))))))))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil())))))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CNil())))))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(FALSE)),
    va_CNil()))), va_CNil()))), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP),
    ARCH_WORD_BYTES, va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))))))))))))
}

lemma{:timeLimitMultiplier 30}
  va_lemma__WimpDrv_Write_eEHCI_USBTDReg_check_new_value(va_b0:va_codes, va_s0:va_state,
  va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__WimpDrv_Write_eEHCI_USBTDReg_check_new_value(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 12 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 2 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    eehci_valid_slot_id(eehci_slot)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var eehci_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    new_usbtd_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0));
    (((ret == TRUE ==> new_usbtd_slot_id == USBTD_SlotID_INVALID ||
    usbtd_map_valid_slot_id(new_usbtd_slot_id)) && (ret == TRUE ==>
    (usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> (var usbtd_flags :=
    usbtd_map_get_flags(va_get_globals(va_sM), new_usbtd_slot_id); usbtd_flags == SetBit(SetBit(0,
    USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit))))) && (ret == TRUE ==>
    (usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> (var eehci_pid :=
    eehci_info_get_pid(va_get_globals(va_sM), eehci_slot); var usbtd_pid :=
    usbtd_map_get_pid(va_get_globals(va_sM), new_usbtd_slot_id); eehci_pid == usbtd_pid)))) && (ret
    == TRUE ==> (usbtd_map_valid_slot_id(new_usbtd_slot_id) ==>
    usbtd_slot_valid_busid(va_get_globals(va_sM), new_usbtd_slot_id) && (var eehci_busid:uint16 :=
    usb_parse_eehci_id(eehci_mem_get_eehci_id(va_get_globals(va_sM), eehci_slot)).bus_id; var
    usbtd_busid:uint16 := usbtd_map_get_busid(va_get_globals(va_sM), new_usbtd_slot_id);
    eehci_busid == usbtd_busid)))
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
  ensures  va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code__WimpDrv_Write_eEHCI_USBTDReg_check_new_value();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b3, va_s3, va_sM);
  ghost var va_b11, va_s11 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EDX),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b11, va_s11, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b13, va_s13 := va_lemma_PUSH_VOID(va_b12, va_s12, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b14, va_s14 := va_lemma_MOV_ToReg(va_b13, va_s13, va_sM, va_op_reg_reg(EAX),
    va_op_word_reg(EDI));
  ghost var va_b15, va_s15 := va_lemma_eehci_info_get_pid(va_b14, va_s14, va_sM,
    va_op_reg_reg(EAX));
  ghost var va_b16, va_s16 := va_lemma_Load(va_b15, va_s15, va_sM, va_op_word_reg(ESI),
    va_op_word_reg(ESP), 0);
  ghost var va_b17, va_s17 := va_lemma_POP_VOID(va_b16, va_s16, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b18, va_s18 := va_lemma_PUSH(va_b17, va_s17, va_sM, va_op_word_reg(EDX));
  ghost var va_b19, va_s19 :=
    va_lemma__WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty1(va_b18, va_s18, va_sM);
  ghost var va_b20, va_s20 := va_lemma_Load(va_b19, va_s19, va_sM, va_op_word_reg(EAX),
    va_op_word_reg(ESP), 0);
  ghost var va_b21, va_s21 := va_lemma_POP_VOID(va_b20, va_s20, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_s22, va_c22, va_b22 := va_lemma_block(va_b21, va_s21, va_sM);
  ghost var va_cond_c22, va_s23:va_state := va_lemma_ifElse(va_get_ifCond(va_c22),
    va_get_ifTrue(va_c22), va_get_ifFalse(va_c22), va_s21, va_s22);
  if (va_cond_c22)
  {
    ghost var va_b24 := va_get_block(va_get_ifTrue(va_c22));
    ghost var va_b25, va_s25 := va_lemma_usbtd_check_td_slot_id(va_b24, va_s23, va_s22,
      va_op_reg_reg(EDX), va_op_reg_reg(EAX));
    ghost var va_s26, va_c26, va_b26 := va_lemma_block(va_b25, va_s25, va_s22);
    ghost var va_cond_c26, va_s27:va_state := va_lemma_ifElse(va_get_ifCond(va_c26),
      va_get_ifTrue(va_c26), va_get_ifFalse(va_c26), va_s25, va_s26);
    if (va_cond_c26)
    {
      ghost var va_b28 := va_get_block(va_get_ifTrue(va_c26));
      ghost var va_b29, va_s29 := va_lemma_PUSH(va_b28, va_s27, va_s26, va_op_word_reg(EDX));
      ghost var va_b30, va_s30 :=
        va_lemma__WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty2(va_b29, va_s29,
        va_s26);
      ghost var va_b31, va_s31 := va_lemma_Load(va_b30, va_s30, va_s26, va_op_word_reg(EAX),
        va_op_word_reg(ESP), 0);
      ghost var va_b32, va_s32 := va_lemma_POP_VOID(va_b31, va_s31, va_s26, 1 * ARCH_WORD_BYTES);
      ghost var va_s33, va_c33, va_b33 := va_lemma_block(va_b32, va_s32, va_s26);
      ghost var va_cond_c33, va_s34:va_state := va_lemma_ifElse(va_get_ifCond(va_c33),
        va_get_ifTrue(va_c33), va_get_ifFalse(va_c33), va_s32, va_s33);
      if (va_cond_c33)
      {
        ghost var va_b35 := va_get_block(va_get_ifTrue(va_c33));
        ghost var va_b36, va_s36 := va_lemma_PUSH(va_b35, va_s34, va_s33, va_op_word_reg(EDX));
        ghost var va_b37, va_s37 := va_lemma_usbtd_get_td_pid(va_b36, va_s36, va_s33);
        ghost var va_b38, va_s38 := va_lemma_Load(va_b37, va_s37, va_s33, va_op_word_reg(ECX),
          va_op_word_reg(ESP), 0);
        ghost var va_b39, va_s39 := va_lemma_POP_VOID(va_b38, va_s38, va_s33, 1 * ARCH_WORD_BYTES);
        ghost var va_s40, va_c40, va_b40 := va_lemma_block(va_b39, va_s39, va_s33);
        ghost var va_cond_c40, va_s41:va_state := va_lemma_ifElse(va_get_ifCond(va_c40),
          va_get_ifTrue(va_c40), va_get_ifFalse(va_c40), va_s39, va_s40);
        if (va_cond_c40)
        {
          ghost var va_b42 := va_get_block(va_get_ifTrue(va_c40));
          ghost var va_b43, va_s43 := va_lemma_PUSH(va_b42, va_s41, va_s40, va_op_word_reg(EDI));
          ghost var va_b44, va_s44 := va_lemma_eehci_mem_read_id(va_b43, va_s43, va_s40);
          ghost var va_b45, va_s45 := va_lemma_Load(va_b44, va_s44, va_s40, va_op_word_reg(EBX),
            va_op_word_reg(ESP), 0);
          ghost var va_b46, va_s46 := va_lemma_POP_VOID(va_b45, va_s45, va_s40, 1 *
            ARCH_WORD_BYTES);
          ghost var va_b47, va_s47 := va_lemma_PUSH(va_b46, va_s46, va_s40, va_op_word_reg(EBX));
          ghost var va_b48, va_s48 := va_lemma_eechi_id_get_bus_id(va_b47, va_s47, va_s40);
          ghost var va_b49, va_s49 := va_lemma_Load(va_b48, va_s48, va_s40, va_op_word_reg(EBX),
            va_op_word_reg(ESP), 0);
          ghost var va_b50, va_s50 := va_lemma_POP_VOID(va_b49, va_s49, va_s40, 1 *
            ARCH_WORD_BYTES);
          ghost var va_b51, va_s51 := va_lemma_PUSH(va_b50, va_s50, va_s40, va_op_word_reg(EDX));
          ghost var va_b52, va_s52 := va_lemma_usbtd_get_bus_id(va_b51, va_s51, va_s40);
          ghost var va_b53, va_s53 := va_lemma_Load(va_b52, va_s52, va_s40, va_op_word_reg(ECX),
            va_op_word_reg(ESP), 0);
          ghost var va_b54, va_s54 := va_lemma_POP_VOID(va_b53, va_s53, va_s40, 1 *
            ARCH_WORD_BYTES);
          ghost var va_s55, va_c55, va_b55 := va_lemma_block(va_b54, va_s54, va_s40);
          ghost var va_cond_c55, va_s56:va_state := va_lemma_ifElse(va_get_ifCond(va_c55),
            va_get_ifTrue(va_c55), va_get_ifFalse(va_c55), va_s54, va_s55);
          if (va_cond_c55)
          {
            ghost var va_b57 := va_get_block(va_get_ifTrue(va_c55));
            ghost var va_b58, va_s58 := va_lemma_Store(va_b57, va_s56, va_s55, va_op_word_reg(EBP),
              ARCH_WORD_BYTES, va_const_word(TRUE));
            va_s55 := va_lemma_empty(va_s58, va_s55);
          }
          else
          {
            ghost var va_b59 := va_get_block(va_get_ifFalse(va_c55));
            ghost var va_b60, va_s60 := va_lemma_Store(va_b59, va_s56, va_s55, va_op_word_reg(EBP),
              ARCH_WORD_BYTES, va_const_word(FALSE));
            va_s55 := va_lemma_empty(va_s60, va_s55);
          }
          va_s40 := va_lemma_empty(va_s55, va_s40);
        }
        else
        {
          ghost var va_b61 := va_get_block(va_get_ifFalse(va_c40));
          ghost var va_b62, va_s62 := va_lemma_Store(va_b61, va_s41, va_s40, va_op_word_reg(EBP),
            ARCH_WORD_BYTES, va_const_word(FALSE));
          va_s40 := va_lemma_empty(va_s62, va_s40);
        }
        va_s33 := va_lemma_empty(va_s40, va_s33);
      }
      else
      {
        ghost var va_b63 := va_get_block(va_get_ifFalse(va_c33));
        ghost var va_b64, va_s64 := va_lemma_Store(va_b63, va_s34, va_s33, va_op_word_reg(EBP),
          ARCH_WORD_BYTES, va_const_word(FALSE));
        va_s33 := va_lemma_empty(va_s64, va_s33);
      }
      va_s26 := va_lemma_empty(va_s33, va_s26);
    }
    else
    {
      ghost var va_b65 := va_get_block(va_get_ifFalse(va_c26));
      ghost var va_b66, va_s66 := va_lemma_Store(va_b65, va_s27, va_s26, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      va_s26 := va_lemma_empty(va_s66, va_s26);
    }
    va_s22 := va_lemma_empty(va_s26, va_s22);
  }
  else
  {
    ghost var va_b67 := va_get_block(va_get_ifFalse(va_c22));
    ghost var va_b68, va_s68 := va_lemma_Store(va_b67, va_s23, va_s22, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s22 := va_lemma_empty(va_s68, va_s22);
  }
  ghost var va_b69, va_s69 := va_lemma_POP_Reg1ToReg6(va_b22, va_s22, va_sM);
  ghost var va_b70, va_s70 := va_lemma_POP_OneReg(va_b69, va_s69, va_sM, va_op_reg_reg(EBP));
  Lemma_modify_regs_stateeq(va_old_s, va_s70);
  va_sM := va_lemma_empty(va_s70, va_sM);
}
//--
//-- _WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty1

function method{:opaque}
  va_code__WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty1():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EDX)),
    va_CCons(va_code_Load(va_op_word_reg(EDX), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_IfElse(va_cmp_ne(va_op_cmp_reg(EDX), va_const_cmp(USBTD_SlotID_INVALID)),
    va_Block(va_CCons(va_code_usbtd_check_td_slot_id(va_op_reg_reg(EDX), va_op_reg_reg(EAX)),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(EAX), va_const_cmp(TRUE)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CNil()))),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil()))), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EDX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil()))))))))
}

lemma va_lemma__WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty1(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0,
    va_code__WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty1(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 3 * ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) -
    stack_req_space) && (var stack_params_space := 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var new_usbtd_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ret == TRUE ==>
    new_usbtd_slot_id == USBTD_SlotID_INVALID || usbtd_map_valid_slot_id(new_usbtd_slot_id)
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
  ensures  va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code__WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty1();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  ghost var va_b2, va_s2 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b3, va_s3 := va_lemma_MOV_ToReg(va_b2, va_s2, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b6, va_s6 := va_lemma_PUSH_TwoRegs(va_b3, va_s3, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EDX));
  ghost var va_b7, va_s7 := va_lemma_Load(va_b6, va_s6, va_sM, va_op_word_reg(EDX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_s8, va_c8, va_b8 := va_lemma_block(va_b7, va_s7, va_sM);
  ghost var va_cond_c8, va_s9:va_state := va_lemma_ifElse(va_get_ifCond(va_c8),
    va_get_ifTrue(va_c8), va_get_ifFalse(va_c8), va_s7, va_s8);
  if (va_cond_c8)
  {
    ghost var va_b10 := va_get_block(va_get_ifTrue(va_c8));
    ghost var va_b11, va_s11 := va_lemma_usbtd_check_td_slot_id(va_b10, va_s9, va_s8,
      va_op_reg_reg(EDX), va_op_reg_reg(EAX));
    ghost var va_s12, va_c12, va_b12 := va_lemma_block(va_b11, va_s11, va_s8);
    ghost var va_cond_c12, va_s13:va_state := va_lemma_ifElse(va_get_ifCond(va_c12),
      va_get_ifTrue(va_c12), va_get_ifFalse(va_c12), va_s11, va_s12);
    if (va_cond_c12)
    {
      ghost var va_b14 := va_get_block(va_get_ifTrue(va_c12));
      ghost var va_b15, va_s15 := va_lemma_Store(va_b14, va_s13, va_s12, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(TRUE));
      va_s12 := va_lemma_empty(va_s15, va_s12);
    }
    else
    {
      ghost var va_b16 := va_get_block(va_get_ifFalse(va_c12));
      ghost var va_b17, va_s17 := va_lemma_Store(va_b16, va_s13, va_s12, va_op_word_reg(EBP),
        ARCH_WORD_BYTES, va_const_word(FALSE));
      va_s12 := va_lemma_empty(va_s17, va_s12);
    }
    va_s8 := va_lemma_empty(va_s12, va_s8);
  }
  else
  {
    ghost var va_b18 := va_get_block(va_get_ifFalse(va_c8));
    ghost var va_b19, va_s19 := va_lemma_Store(va_b18, va_s9, va_s8, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    va_s8 := va_lemma_empty(va_s19, va_s8);
  }
  ghost var va_b20, va_s20 := va_lemma_POP_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EDX));
  ghost var va_b21, va_s21 := va_lemma_POP_OneReg(va_b20, va_s20, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s21, va_sM);
}
//--
//-- _WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty2

function method{:opaque}
  va_code__WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty2():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_code_PUSH_TwoRegs(va_op_reg_reg(ECX), va_op_reg_reg(EDX)),
    va_CCons(va_code_Load(va_op_word_reg(EBX), va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_usbtd_get_flags(),
    va_CCons(va_code_Load(va_op_word_reg(ECX), va_op_word_reg(ESP), 0), va_CCons(va_code_POP_VOID(1
    * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX), va_const_word(0)),
    va_CCons(va_code_SetBit(va_op_word_reg(EDX), USBTD_SLOT_FLAG_SubmitDone_Bit),
    va_CCons(va_code_SetBit(va_op_word_reg(EDX), USBTD_SLOT_FLAG_SlotSecure_Bit),
    va_CCons(va_IfElse(va_cmp_eq(va_op_cmp_reg(ECX), va_op_cmp_reg(EDX)),
    va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES, va_const_word(TRUE)),
    va_CNil())), va_Block(va_CCons(va_code_Store(va_op_word_reg(EBP), ARCH_WORD_BYTES,
    va_const_word(FALSE)), va_CNil()))), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(ECX),
    va_op_reg_reg(EDX)), va_CCons(va_code_POP_TwoRegs(va_op_reg_reg(EAX), va_op_reg_reg(EBX)),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)), va_CNil())))))))))))))))))
}

lemma va_lemma__WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty2(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0,
    va_code__WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty2(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 5 * ARCH_WORD_BYTES + 6 * ARCH_WORD_BYTES + 1 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 1 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space))
  requires var new_usbtd_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    usbtd_map_valid_slot_id(new_usbtd_slot_id)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var new_usbtd_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    var ret:word := stack_get_val(va_get_mem(va_sM), va_get_reg(ESP, va_s0)); ret == TRUE ==> (var
    usbtd_flags := usbtd_map_get_flags(va_get_globals(va_s0), new_usbtd_slot_id); usbtd_flags ==
    SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit))
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
  ensures  va_get_globals(va_sM) == va_get_globals(va_s0)
  ensures  va_state_eq(va_sM, va_update_reg(EBP, va_sM, va_update_reg(ESP, va_sM,
    va_update_reg(EDI, va_sM, va_update_reg(ESI, va_sM, va_update_reg(EDX, va_sM,
    va_update_reg(ECX, va_sM, va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM,
    va_update_mem(va_sM, va_update_ok(va_sM, va_s0)))))))))))
{
  reveal_va_code__WimpDrv_Write_eEHCI_USBTDReg_check_new_value_CheckProperty2();
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
  ghost var va_b9, va_s9 := va_lemma_PUSH_TwoRegs(va_b8, va_s8, va_sM, va_op_reg_reg(ECX),
    va_op_reg_reg(EDX));
  ghost var va_b10, va_s10 := va_lemma_Load(va_b9, va_s9, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var va_b11, va_s11 := va_lemma_PUSH(va_b10, va_s10, va_sM, va_op_word_reg(EBX));
  ghost var va_b12, va_s12 := va_lemma_usbtd_get_flags(va_b11, va_s11, va_sM);
  ghost var va_b13, va_s13 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(ESP), 0);
  ghost var va_b14, va_s14 := va_lemma_POP_VOID(va_b13, va_s13, va_sM, 1 * ARCH_WORD_BYTES);
  ghost var va_b15, va_s15 := va_lemma_MOV_ToReg(va_b14, va_s14, va_sM, va_op_reg_reg(EDX),
    va_const_word(0));
  ghost var va_b16, va_s16 := va_lemma_SetBit(va_b15, va_s15, va_sM, va_op_word_reg(EDX),
    USBTD_SLOT_FLAG_SubmitDone_Bit);
  ghost var va_b17, va_s17 := va_lemma_SetBit(va_b16, va_s16, va_sM, va_op_word_reg(EDX),
    USBTD_SLOT_FLAG_SlotSecure_Bit);
  ghost var va_s18, va_c18, va_b18 := va_lemma_block(va_b17, va_s17, va_sM);
  ghost var va_cond_c18, va_s19:va_state := va_lemma_ifElse(va_get_ifCond(va_c18),
    va_get_ifTrue(va_c18), va_get_ifFalse(va_c18), va_s17, va_s18);
  if (va_cond_c18)
  {
    ghost var va_b20 := va_get_block(va_get_ifTrue(va_c18));
    ghost var va_b21, va_s21 := va_lemma_Store(va_b20, va_s19, va_s18, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(TRUE));
    va_s18 := va_lemma_empty(va_s21, va_s18);
  }
  else
  {
    ghost var va_b22 := va_get_block(va_get_ifFalse(va_c18));
    ghost var va_b23, va_s23 := va_lemma_Store(va_b22, va_s19, va_s18, va_op_word_reg(EBP),
      ARCH_WORD_BYTES, va_const_word(FALSE));
    va_s18 := va_lemma_empty(va_s23, va_s18);
  }
  ghost var va_b24, va_s24 := va_lemma_POP_TwoRegs(va_b18, va_s18, va_sM, va_op_reg_reg(ECX),
    va_op_reg_reg(EDX));
  ghost var va_b25, va_s25 := va_lemma_POP_TwoRegs(va_b24, va_s24, va_sM, va_op_reg_reg(EAX),
    va_op_reg_reg(EBX));
  ghost var va_b26, va_s26 := va_lemma_POP_OneReg(va_b25, va_s25, va_sM, va_op_reg_reg(EBP));
  va_sM := va_lemma_empty(va_s26, va_sM);
}
//--
