include "../../../ins/x86/ins_wrapper.gen.dfy"
include "../usb_tds_utils.gen.dfy"
include "../../../partition_id_ops.gen.dfy"
include "../eehci_info.gen.dfy"
include "..\\usb_tds_utils.i.dfy"
//-- _usbtd_slot_submit_partial_otherfields

function method{:opaque} va_code__usbtd_slot_submit_partial_otherfields():va_code
{
  va_Block(va_CCons(va_code_PUSH_OneReg(va_op_reg_reg(EBP)),
    va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EBP), va_op_word_reg(ESP)),
    va_CCons(va_code_PUSH_Reg1ToReg6(), va_CCons(va_code_Load(va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 7 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_usbtd_set_bus_id(),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_PUSH(va_const_word(G_USBTDs_MAP_ENTRY_InputParam1)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_usbtd_set_inputparams(),
    va_CCons(va_code_POP_VOID(3 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_PUSH(va_const_word(G_USBTDs_MAP_ENTRY_InputParam2)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_usbtd_set_inputparams(),
    va_CCons(va_code_POP_VOID(3 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(ECX),
    va_op_word_reg(EBP), 6 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(ECX)),
    va_CCons(va_code_PUSH(va_const_word(G_USBTDs_MAP_ENTRY_InputParam3)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_usbtd_set_inputparams(),
    va_CCons(va_code_POP_VOID(3 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_usbtd_set_wimpdrv_slotid(),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES), va_CCons(va_code_Load(va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES), va_CCons(va_code_PUSH(va_op_word_reg(EDI)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_usbtd_set_usbpdev_slotid(),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES), va_CCons(va_code_MOV_ToReg(va_op_reg_reg(EDX),
    va_const_word(0)), va_CCons(va_code_SetBit(va_op_word_reg(EDX),
    USBTD_SLOT_FLAG_SubmitDone_Bit), va_CCons(va_code_PUSH(va_op_word_reg(EDX)),
    va_CCons(va_code_PUSH(va_op_word_reg(EBX)), va_CCons(va_code_usbtd_set_flags(),
    va_CCons(va_code_POP_VOID(2 * ARCH_WORD_BYTES), va_CCons(va_code_POP_Reg1ToReg6(),
    va_CCons(va_code_POP_OneReg(va_op_reg_reg(EBP)),
    va_CNil()))))))))))))))))))))))))))))))))))))))))))))))
}

lemma{:timeLimitMultiplier 120} va_lemma__usbtd_slot_submit_partial_otherfields(va_b0:va_codes,
  va_s0:va_state, va_sN:va_state)
  returns (va_bM:va_codes, va_sM:va_state)
  requires va_require(va_b0, va_code__usbtd_slot_submit_partial_otherfields(), va_s0, va_sN)
  ensures  va_ensure(va_b0, va_bM, va_s0, va_sM, va_sN)
  requires va_get_ok(va_s0)
  ensures  va_get_ok(va_sM)
  requires InstSaneState(va_s0)
  ensures  InstSaneState(va_sM)
  requires var stack_req_space := 7 * ARCH_WORD_BYTES + 7 * ARCH_WORD_BYTES + 3 * ARCH_WORD_BYTES;
    IsAddrInStack(va_get_reg(ESP, va_s0) - stack_req_space) && (var stack_params_space := 7 *
    ARCH_WORD_BYTES; IsAddrInStack(va_get_reg(ESP, va_s0) + stack_params_space - ARCH_WORD_BYTES))
  requires var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    (usbtd_map_valid_slot_id(td_slot) && eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_s0),
    td_slot)) && usbtds_verifiedtds_do_not_associate_usbtd(va_get_globals(va_s0), td_slot)
  requires var usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 2 *
    ARCH_WORD_BYTES); usbpdev_slot == WimpUSBPDev_SlotID_EMPTY ||
    usbpdev_valid_slot_id(usbpdev_slot)
  requires var wimpdrv_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1
    * ARCH_WORD_BYTES); wimpdrv_valid_slot_id(wimpdrv_slot_id)
  requires var bus_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 6 *
    ARCH_WORD_BYTES); usb_is_valid_bus_id(bus_id)
  requires var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    flags := usbtd_map_get_flags(va_get_globals(va_s0), td_slot); TestBit(flags,
    USBTD_SLOT_FLAG_SlotSecure_Bit) == false
  requires WSM_physical_EHCIs_must_be_inactive(va_s0.subjects, va_s0.activate_conds)
  requires !(interrupts_enabled(va_get_sreg(EFLAGS, va_s0)))
  ensures  var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0)); var
    wimpdrv_slot_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 1 *
    ARCH_WORD_BYTES); var usbpdev_slot:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP,
    va_s0) + 2 * ARCH_WORD_BYTES); var input_param1:uint32 := stack_get_val(va_get_mem(va_s0),
    va_get_reg(ESP, va_s0) + 3 * ARCH_WORD_BYTES); var input_param2:uint32 :=
    stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 4 * ARCH_WORD_BYTES); var
    input_param3:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) + 5 *
    ARCH_WORD_BYTES); var bus_id:word := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0) +
    6 * ARCH_WORD_BYTES); (((((((usbtd_map_get_busid(va_get_globals(va_sM), td_slot) == bus_id &&
    usbtd_map_get_wimpdrv_slotid(va_get_globals(va_sM), td_slot) == wimpdrv_slot_id) &&
    usbtd_map_get_usbpdev_slotid(va_get_globals(va_sM), td_slot) == usbpdev_slot) &&
    usbtd_map_get_inputparam(va_get_globals(va_sM), td_slot, G_USBTDs_MAP_ENTRY_InputParam1) ==
    input_param1) && usbtd_map_get_inputparam(va_get_globals(va_sM), td_slot,
    G_USBTDs_MAP_ENTRY_InputParam2) == input_param2) &&
    usbtd_map_get_inputparam(va_get_globals(va_sM), td_slot, G_USBTDs_MAP_ENTRY_InputParam3) ==
    input_param3) && p_usbtd_slot_submit_usbtd_ret_global(va_get_globals(va_s0),
    va_get_globals(va_sM), td_slot)) && p_usbtd_content_equal(va_get_globals(va_s0),
    va_get_globals(va_sM), td_slot)) && usbtd_map_get_type(va_get_globals(va_sM), td_slot) ==
    usbtd_map_get_type(va_get_globals(va_s0), td_slot)
  ensures  var td_slot:uint32 := stack_get_val(va_get_mem(va_s0), va_get_reg(ESP, va_s0));
    eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_sM), td_slot)
  ensures  va_get_reg(ESP, va_sM) == va_get_reg(ESP, va_s0)
  ensures  va_get_reg(EBP, va_sM) == va_get_reg(EBP, va_s0)
  ensures  va_get_reg(EDI, va_sM) == va_get_reg(EDI, va_s0)
  ensures  va_get_reg(ESI, va_sM) == va_get_reg(ESI, va_s0)
  ensures  va_get_reg(EAX, va_sM) == va_get_reg(EAX, va_s0)
  ensures  va_get_reg(EBX, va_sM) == va_get_reg(EBX, va_s0)
  ensures  va_get_reg(ECX, va_sM) == va_get_reg(ECX, va_s0)
  ensures  va_get_reg(EDX, va_sM) == va_get_reg(EDX, va_s0)
  ensures  stack_under_sp_is_unchanged(va_get_mem(va_s0), va_get_mem(va_sM), va_get_reg(ESP, va_sM))
  ensures  is_flags_unchanged(va_get_sreg(EFLAGS, va_s0), va_get_sreg(EFLAGS, va_sM))
  ensures  state_equal_except_mstate(va_s0, va_sM)
  ensures  va_state_eq(va_sM, va_update_reg(EDX, va_sM, va_update_reg(ECX, va_sM,
    va_update_reg(EBX, va_sM, va_update_reg(EAX, va_sM, va_update_reg(EDI, va_sM,
    va_update_reg(ESI, va_sM, va_update_mem(va_sM, va_update_reg(ESP, va_sM, va_update_reg(EBP,
    va_sM, va_update_globals(va_sM, va_update_ok(va_sM, va_s0))))))))))))
{
  reveal_va_code__usbtd_slot_submit_partial_otherfields();
  var va_old_s:va_state := va_s0;
  ghost var va_ltmp1, va_cM:va_code, va_ltmp2 := va_lemma_block(va_b0, va_s0, va_sN);
  va_sM := va_ltmp1;
  va_bM := va_ltmp2;
  var va_b1:va_codes := va_get_block(va_cM);
  reveal_WordAligned();
  ghost var va_b3, va_s3 := va_lemma_PUSH_OneReg(va_b1, va_s0, va_sM, va_op_reg_reg(EBP));
  ghost var va_b4, va_s4 := va_lemma_MOV_ToReg(va_b3, va_s3, va_sM, va_op_reg_reg(EBP),
    va_op_word_reg(ESP));
  ghost var va_b10, va_s10 := va_lemma_PUSH_Reg1ToReg6(va_b4, va_s4, va_sM);
  ghost var orig_esp := va_get_reg(ESP, va_s10);
  ghost var va_b12, va_s12 := va_lemma_Load(va_b10, va_s10, va_sM, va_op_word_reg(EBX),
    va_op_word_reg(EBP), 1 * ARCH_WORD_BYTES);
  ghost var in_td_slot := va_get_reg(EBX, va_s12);
  ghost var globals1 := va_get_globals(va_s12);
  ghost var va_b15, va_s15 := va_lemma_Load(va_b12, va_s12, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 7 * ARCH_WORD_BYTES);
  ghost var va_b16, va_s16 := va_lemma_PUSH(va_b15, va_s15, va_sM, va_op_word_reg(EDI));
  ghost var bus_id := va_get_reg(EDI, va_s16);
  ghost var va_b18, va_s18 := va_lemma_PUSH(va_b16, va_s16, va_sM, va_op_word_reg(EBX));
  ghost var va_b19, va_s19 := va_lemma_usbtd_set_bus_id(va_b18, va_s18, va_sM);
  ghost var globals2 := va_get_globals(va_s19);
  ghost var va_b21, va_s21 := va_lemma_POP_VOID(va_b19, va_s19, va_sM, 2 * ARCH_WORD_BYTES);
  Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(in_td_slot,
    G_USBTDs_MAP_ENTRY_BUSID_BytesOffset);
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals1, globals2, in_td_slot,
    G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, bus_id);
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals1, globals2, in_td_slot,
    G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, bus_id);
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals1, globals2, in_td_slot,
    G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, bus_id);
  Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals1, globals2, in_td_slot,
    G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, bus_id);
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(globals1, globals2, in_td_slot,
    G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, bus_id);
  Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals1, globals2, in_td_slot,
    G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, bus_id);
  assert global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2,
    G_EEHCI_MEM());  // line 133 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  Lemma_usbtds_verifiedtds_do_not_associate_usbtd_HoldIfModifyingUSBTDRemainsInsecure(globals1,
    globals2, in_td_slot);
  assert usbtds_verifiedtds_do_not_associate_usbtd(globals2, in_td_slot);  // line 135 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  ghost var va_b32, va_s32 := va_lemma_Load(va_b21, va_s21, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 4 * ARCH_WORD_BYTES);
  ghost var va_b33, va_s33 := va_lemma_PUSH(va_b32, va_s32, va_sM, va_op_word_reg(EDI));
  ghost var new_input_param1 := va_get_reg(EDI, va_s33);
  ghost var va_b35, va_s35 := va_lemma_PUSH(va_b33, va_s33, va_sM,
    va_const_word(G_USBTDs_MAP_ENTRY_InputParam1));
  ghost var va_b36, va_s36 := va_lemma_PUSH(va_b35, va_s35, va_sM, va_op_word_reg(EBX));
  ghost var va_b37, va_s37 := va_lemma_usbtd_set_inputparams(va_b36, va_s36, va_sM);
  ghost var globals3 := va_get_globals(va_s37);
  ghost var va_b39, va_s39 := va_lemma_POP_VOID(va_b37, va_s37, va_sM, 3 * ARCH_WORD_BYTES);
  Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset);
  Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals2, globals3, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset, new_input_param1);
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals2, globals3, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset, new_input_param1);
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals2, globals3, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset, new_input_param1);
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals2, globals3, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset, new_input_param1);
  Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals2, globals3, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset, new_input_param1);
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(globals2, globals3, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset, new_input_param1);
  Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals2, globals3, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset, new_input_param1);
  assert global_read_fullval(globals2, G_EEHCI_MEM()) == global_read_fullval(globals3,
    G_EEHCI_MEM());  // line 155 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  Lemma_usbtds_verifiedtds_do_not_associate_usbtd_HoldIfModifyingUSBTDRemainsInsecure(globals2,
    globals3, in_td_slot);
  assert usbtds_verifiedtds_do_not_associate_usbtd(globals3, in_td_slot);  // line 157 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert InstSaneState(va_s39);  // line 159 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  ghost var va_b52, va_s52 := va_lemma_Load(va_b39, va_s39, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 5 * ARCH_WORD_BYTES);
  ghost var va_b53, va_s53 := va_lemma_PUSH(va_b52, va_s52, va_sM, va_op_word_reg(EDI));
  ghost var new_input_param2 := va_get_reg(EDI, va_s53);
  ghost var va_b55, va_s55 := va_lemma_PUSH(va_b53, va_s53, va_sM,
    va_const_word(G_USBTDs_MAP_ENTRY_InputParam2));
  ghost var va_b56, va_s56 := va_lemma_PUSH(va_b55, va_s55, va_sM, va_op_word_reg(EBX));
  ghost var va_b57, va_s57 := va_lemma_usbtd_set_inputparams(va_b56, va_s56, va_sM);
  ghost var globals4 := va_get_globals(va_s57);
  ghost var va_b59, va_s59 := va_lemma_POP_VOID(va_b57, va_s57, va_sM, 3 * ARCH_WORD_BYTES);
  Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset);
  Lemma_WK_USB_TD_Map_PreserveInputParam1FieldIfModifyOtherFields(globals3, globals4, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, new_input_param2);
  Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals3, globals4, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, new_input_param2);
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals3, globals4, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, new_input_param2);
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals3, globals4, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, new_input_param2);
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals3, globals4, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, new_input_param2);
  Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals3, globals4, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, new_input_param2);
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(globals3, globals4, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, new_input_param2);
  Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals3, globals4, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, new_input_param2);
  assert global_read_fullval(globals3, G_EEHCI_MEM()) == global_read_fullval(globals4,
    G_EEHCI_MEM());  // line 178 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  Lemma_usbtds_verifiedtds_do_not_associate_usbtd_HoldIfModifyingUSBTDRemainsInsecure(globals3,
    globals4, in_td_slot);
  assert usbtds_verifiedtds_do_not_associate_usbtd(globals4, in_td_slot);  // line 180 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert InstSaneState(va_s59);  // line 182 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  ghost var va_b73, va_s73 := va_lemma_Load(va_b59, va_s59, va_sM, va_op_word_reg(ECX),
    va_op_word_reg(EBP), 6 * ARCH_WORD_BYTES);
  ghost var va_b74, va_s74 := va_lemma_PUSH(va_b73, va_s73, va_sM, va_op_word_reg(ECX));
  ghost var new_input_param3 := va_get_reg(ECX, va_s74);
  ghost var va_b76, va_s76 := va_lemma_PUSH(va_b74, va_s74, va_sM,
    va_const_word(G_USBTDs_MAP_ENTRY_InputParam3));
  ghost var va_b77, va_s77 := va_lemma_PUSH(va_b76, va_s76, va_sM, va_op_word_reg(EBX));
  ghost var va_b78, va_s78 := va_lemma_usbtd_set_inputparams(va_b77, va_s77, va_sM);
  ghost var globals5 := va_get_globals(va_s78);
  ghost var va_b80, va_s80 := va_lemma_POP_VOID(va_b78, va_s78, va_sM, 3 * ARCH_WORD_BYTES);
  Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);
  Lemma_WK_USB_TD_Map_PreserveInputParam2FieldIfModifyOtherFields(globals4, globals5, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_input_param3);
  Lemma_WK_USB_TD_Map_PreserveInputParam1FieldIfModifyOtherFields(globals4, globals5, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_input_param3);
  Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals4, globals5, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_input_param3);
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals4, globals5, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_input_param3);
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals4, globals5, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_input_param3);
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals4, globals5, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_input_param3);
  Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals4, globals5, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_input_param3);
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(globals4, globals5, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_input_param3);
  Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals4, globals5, in_td_slot,
    G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_input_param3);
  assert global_read_fullval(globals4, G_EEHCI_MEM()) == global_read_fullval(globals5,
    G_EEHCI_MEM());  // line 204 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  Lemma_usbtds_verifiedtds_do_not_associate_usbtd_HoldIfModifyingUSBTDRemainsInsecure(globals4,
    globals5, in_td_slot);
  assert usbtds_verifiedtds_do_not_associate_usbtd(globals5, in_td_slot);  // line 206 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert usbtd_map_get_inputparam(va_get_globals(va_s80), in_td_slot,
    G_USBTDs_MAP_ENTRY_InputParam1) == new_input_param1;  // line 209 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert usbtd_map_get_inputparam(va_get_globals(va_s80), in_td_slot,
    G_USBTDs_MAP_ENTRY_InputParam2) == new_input_param2;  // line 210 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert usbtd_map_get_inputparam(va_get_globals(va_s80), in_td_slot,
    G_USBTDs_MAP_ENTRY_InputParam3) == new_input_param3;  // line 211 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  ghost var va_b97, va_s97 := va_lemma_Load(va_b80, va_s80, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 2 * ARCH_WORD_BYTES);
  ghost var va_b98, va_s98 := va_lemma_PUSH(va_b97, va_s97, va_sM, va_op_word_reg(EDI));
  ghost var wimpdrv_slot_id := va_get_reg(EDI, va_s98);
  ghost var va_b100, va_s100 := va_lemma_PUSH(va_b98, va_s98, va_sM, va_op_word_reg(EBX));
  ghost var va_b101, va_s101 := va_lemma_usbtd_set_wimpdrv_slotid(va_b100, va_s100, va_sM);
  ghost var globals6 := va_get_globals(va_s101);
  ghost var va_b103, va_s103 := va_lemma_POP_VOID(va_b101, va_s101, va_sM, 2 * ARCH_WORD_BYTES);
  Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(in_td_slot,
    G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset);
  Lemma_WK_USB_TD_Map_PreserveInputParam3FieldIfModifyOtherFields(globals5, globals6, in_td_slot,
    G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, wimpdrv_slot_id);
  Lemma_WK_USB_TD_Map_PreserveInputParam2FieldIfModifyOtherFields(globals5, globals6, in_td_slot,
    G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, wimpdrv_slot_id);
  Lemma_WK_USB_TD_Map_PreserveInputParam1FieldIfModifyOtherFields(globals5, globals6, in_td_slot,
    G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, wimpdrv_slot_id);
  Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals5, globals6, in_td_slot,
    G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, wimpdrv_slot_id);
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals5, globals6, in_td_slot,
    G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, wimpdrv_slot_id);
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals5, globals6, in_td_slot,
    G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, wimpdrv_slot_id);
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals5, globals6, in_td_slot,
    G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, wimpdrv_slot_id);
  Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals5, globals6, in_td_slot,
    G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, wimpdrv_slot_id);
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(globals5, globals6, in_td_slot,
    G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, wimpdrv_slot_id);
  Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals5, globals6, in_td_slot,
    G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, wimpdrv_slot_id);
  assert global_read_fullval(globals5, G_EEHCI_MEM()) == global_read_fullval(globals6,
    G_EEHCI_MEM());  // line 234 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  Lemma_usbtds_verifiedtds_do_not_associate_usbtd_HoldIfModifyingUSBTDRemainsInsecure(globals5,
    globals6, in_td_slot);
  assert usbtds_verifiedtds_do_not_associate_usbtd(globals6, in_td_slot);  // line 236 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  ghost var va_b118, va_s118 := va_lemma_Load(va_b103, va_s103, va_sM, va_op_word_reg(EDI),
    va_op_word_reg(EBP), 3 * ARCH_WORD_BYTES);
  ghost var va_b119, va_s119 := va_lemma_PUSH(va_b118, va_s118, va_sM, va_op_word_reg(EDI));
  ghost var usbpdev_slot := va_get_reg(EDI, va_s119);
  ghost var va_b121, va_s121 := va_lemma_PUSH(va_b119, va_s119, va_sM, va_op_word_reg(EBX));
  assert va_get_reg(EBX, va_s121) == in_td_slot;  // line 243 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert usbtd_map_valid_slot_id(va_get_reg(EBX, va_s121));  // line 244 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  ghost var va_b124, va_s124 := va_lemma_usbtd_set_usbpdev_slotid(va_b121, va_s121, va_sM);
  ghost var globals7 := va_get_globals(va_s124);
  ghost var va_b126, va_s126 := va_lemma_POP_VOID(va_b124, va_s124, va_sM, 2 * ARCH_WORD_BYTES);
  Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(in_td_slot,
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset);
  Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(globals6, globals7, in_td_slot,
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, usbpdev_slot);
  Lemma_WK_USB_TD_Map_PreserveInputParam3FieldIfModifyOtherFields(globals6, globals7, in_td_slot,
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, usbpdev_slot);
  Lemma_WK_USB_TD_Map_PreserveInputParam2FieldIfModifyOtherFields(globals6, globals7, in_td_slot,
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, usbpdev_slot);
  Lemma_WK_USB_TD_Map_PreserveInputParam1FieldIfModifyOtherFields(globals6, globals7, in_td_slot,
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, usbpdev_slot);
  Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals6, globals7, in_td_slot,
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, usbpdev_slot);
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals6, globals7, in_td_slot,
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, usbpdev_slot);
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals6, globals7, in_td_slot,
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, usbpdev_slot);
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals6, globals7, in_td_slot,
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, usbpdev_slot);
  Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals6, globals7, in_td_slot,
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, usbpdev_slot);
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(globals6, globals7, in_td_slot,
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, usbpdev_slot);
  Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals6, globals7, in_td_slot,
    G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, usbpdev_slot);
  assert global_read_fullval(globals6, G_EEHCI_MEM()) == global_read_fullval(globals7,
    G_EEHCI_MEM());  // line 261 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert global_read_fullval(va_get_globals(va_old_s), G_EEHCI_MEM()) ==
    global_read_fullval(globals7, G_EEHCI_MEM());  // line 262 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  Lemma_eehci_mem_no_ref_to_usbtd_slot_Equivilant(va_get_globals(va_old_s), globals7,
    va_get_reg(EBX, va_s126));
  assert eehci_mem_no_ref_to_usbtd_slot(globals7, va_get_reg(EBX, va_s126));  // line 264 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  Lemma_usbtds_verifiedtds_do_not_associate_usbtd_HoldIfModifyingUSBTDRemainsInsecure(globals6,
    globals7, in_td_slot);
  assert usbtds_verifiedtds_do_not_associate_usbtd(globals7, in_td_slot);  // line 266 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert InstSaneState(va_s126);  // line 269 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  ghost var va_b146, va_s146 := va_lemma_MOV_ToReg(va_b126, va_s126, va_sM, va_op_reg_reg(EDX),
    va_const_word(0));
  ghost var va_b147, va_s147 := va_lemma_SetBit(va_b146, va_s146, va_sM, va_op_word_reg(EDX),
    USBTD_SLOT_FLAG_SubmitDone_Bit);
  ghost var va_b148, va_s148 := va_lemma_PUSH(va_b147, va_s147, va_sM, va_op_word_reg(EDX));
  ghost var new_flags := va_get_reg(EDX, va_s148);
  ghost var va_b150, va_s150 := va_lemma_PUSH(va_b148, va_s148, va_sM, va_op_word_reg(EBX));
  assert va_get_reg(EBX, va_s150) == in_td_slot;  // line 275 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert usbtd_map_valid_slot_id(va_get_reg(EBX, va_s150));  // line 276 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  Lemma_TestBit_ReturnFalseIfANumberIs0();
  Lemma_TestBit_ReturnFalse_IfBitNotSetAndAfterSetOtherBits(USBTD_SLOT_FLAG_SlotSecure_Bit);
  assert TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit) == false;  // line 279 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert usbtds_verifiedtds_do_not_associate_usbtd(va_get_globals(va_s150), va_get_reg(EBX,
    va_s150));  // line 280 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  ghost var va_b157, va_s157 := va_lemma_usbtd_set_flags(va_b150, va_s150, va_sM);
  ghost var va_b158, va_s158 := va_lemma_POP_VOID(va_b157, va_s157, va_sM, 2 * ARCH_WORD_BYTES);
  assert va_get_reg(ESP, va_s158) == orig_esp;  // line 283 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  ghost var globals8 := va_get_globals(va_s158);
  Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(in_td_slot,
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset);
  Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(globals7, globals8, in_td_slot,
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
  Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(globals7, globals8, in_td_slot,
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
  Lemma_WK_USB_TD_Map_PreserveInputParam3FieldIfModifyOtherFields(globals7, globals8, in_td_slot,
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
  Lemma_WK_USB_TD_Map_PreserveInputParam2FieldIfModifyOtherFields(globals7, globals8, in_td_slot,
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
  Lemma_WK_USB_TD_Map_PreserveInputParam1FieldIfModifyOtherFields(globals7, globals8, in_td_slot,
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
  Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals7, globals8, in_td_slot,
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
  Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals7, globals8, in_td_slot,
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
  Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals7, globals8, in_td_slot,
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
  Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals7, globals8, in_td_slot,
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
  Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(globals7, globals8, in_td_slot,
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
  Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals7, globals8, in_td_slot,
    G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
  assert global_read_fullval(globals7, G_EEHCI_MEM()) == global_read_fullval(globals8,
    G_EEHCI_MEM());  // line 299 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert global_read_fullval(va_get_globals(va_old_s), G_EEHCI_MEM()) ==
    global_read_fullval(globals8, G_EEHCI_MEM());  // line 300 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  Lemma_eehci_mem_no_ref_to_usbtd_slot_Equivilant(va_get_globals(va_old_s),
    va_get_globals(va_s158), va_get_reg(EBX, va_s158));
  assert eehci_mem_no_ref_to_usbtd_slot(va_get_globals(va_s158), va_get_reg(EBX, va_s158));  // line 302 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  ghost var va_b177, va_s177 := va_lemma_POP_Reg1ToReg6(va_b158, va_s158, va_sM);
  ghost var va_b178, va_s178 := va_lemma_POP_OneReg(va_b177, va_s177, va_sM, va_op_reg_reg(EBP));
  assert usbtd_map_get_wimpdrv_slotid(va_get_globals(va_s178), in_td_slot) == wimpdrv_slot_id;  // line 308 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert usbtd_map_get_usbpdev_slotid(va_get_globals(va_s178), in_td_slot) == usbpdev_slot;  // line 309 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert usbtd_map_get_inputparam(va_get_globals(va_s178), in_td_slot,
    G_USBTDs_MAP_ENTRY_InputParam1) == new_input_param1;  // line 310 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert usbtd_map_get_inputparam(va_get_globals(va_s178), in_td_slot,
    G_USBTDs_MAP_ENTRY_InputParam2) == new_input_param2;  // line 311 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  assert usbtd_map_get_inputparam(va_get_globals(va_s178), in_td_slot,
    G_USBTDs_MAP_ENTRY_InputParam3) == new_input_param3;  // line 312 column 5 of file .\dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.vad
  Lemma__usbtd_slot_submit_partial_otherfields_ProveProperty2And3(va_get_globals(va_old_s),
    globals1, globals2, globals3, globals4, globals5, globals6, globals7, va_get_globals(va_s178),
    in_td_slot);
  Lemma_modify_regs_stateeq(va_old_s, va_s178);
  va_sM := va_lemma_empty(va_s178, va_sM);
}
//--
// Prove the property 2 and 3 of <_usbtd_slot_submit_partial_otherfields>
lemma Lemma__usbtd_slot_submit_partial_otherfields_ProveProperty2And3(
    old_globals:globalsmap, globals1:globalsmap, globals2:globalsmap, globals3:globalsmap, globals4:globalsmap, globals5:globalsmap, 
    globals6:globalsmap, globals7:globalsmap, new_globals:globalsmap, slot:uint32
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(globals3)
    requires WK_ValidGlobalVars_Decls(globals4)
    requires WK_ValidGlobalVars_Decls(globals5)
    requires WK_ValidGlobalVars_Decls(globals6)
    requires WK_ValidGlobalVars_Decls(globals7)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbtd_map_valid_slot_id(slot)

    requires old_globals == globals1
    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != slot
        ==> p_usbtd_equal(globals1, globals2, i)
    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != slot
        ==> p_usbtd_equal(globals2, globals3, i)
    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != slot
        ==> p_usbtd_equal(globals3, globals4, i)
    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != slot
        ==> p_usbtd_equal(globals4, globals5, i)
    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != slot
        ==> p_usbtd_equal(globals5, globals6, i)
    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != slot
        ==> p_usbtd_equal(globals6, globals7, i)
    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != slot
        ==> p_usbtd_equal(globals7, new_globals, i)

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> p_usbtd_content_equal(globals1, globals2, i)
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> p_usbtd_content_equal(globals2, globals3, i)
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> p_usbtd_content_equal(globals3, globals4, i)
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> p_usbtd_content_equal(globals4, globals5, i)
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> p_usbtd_content_equal(globals5, globals6, i)
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> p_usbtd_content_equal(globals6, globals7, i)
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> p_usbtd_content_equal(globals7, new_globals, i)

    ensures forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != slot
        ==> p_usbtd_equal(old_globals, new_globals, i)
    ensures p_usbtd_content_equal(old_globals, new_globals, slot)
{
    reveal p_usbtd_content_equal();

    forall i:uint32 | usbtd_map_valid_slot_id(i) && i != slot
        ensures p_usbtd_equal(old_globals, new_globals, i)
    {
        Lemma_p_usbtd_equal_transitive(old_globals, globals1, globals2, i);
        Lemma_p_usbtd_equal_transitive(old_globals, globals2, globals3, i);
        Lemma_p_usbtd_equal_transitive(old_globals, globals3, globals4, i);
        Lemma_p_usbtd_equal_transitive(old_globals, globals4, globals5, i);
        Lemma_p_usbtd_equal_transitive(old_globals, globals5, globals6, i);
        Lemma_p_usbtd_equal_transitive(old_globals, globals6, globals7, i);
        Lemma_p_usbtd_equal_transitive(old_globals, globals7, new_globals, i);
    }

    Lemma_p_usbtd_content_equal_transitive(old_globals, globals1, globals2, slot);
    Lemma_p_usbtd_content_equal_transitive(old_globals, globals2, globals3, slot);
    Lemma_p_usbtd_content_equal_transitive(old_globals, globals3, globals4, slot);
    Lemma_p_usbtd_content_equal_transitive(old_globals, globals4, globals5, slot);
    Lemma_p_usbtd_content_equal_transitive(old_globals, globals5, globals6, slot);
    Lemma_p_usbtd_content_equal_transitive(old_globals, globals6, globals7, slot);
    Lemma_p_usbtd_content_equal_transitive(old_globals, globals7, new_globals, slot);
}
