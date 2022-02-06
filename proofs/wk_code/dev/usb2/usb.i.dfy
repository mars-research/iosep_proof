include "usb_def.dfy"
include "../../mm/wk_globals.dfy"
include "usb_tds.s.dfy"
include "usb_tds_nlarith.i.dfy"

/*********************** Lemmas for usb_tds_checks.vad ********************/
// [Math] Axiom (well known): One can use proof by contradiction; i.e., a = 128k + m (m != 0)
lemma {:axiom} Lemma_usbtd_paddr_alignment_EquivilantImplOfTestOfMod(a:uint32)
    requires BitwiseAnd(a,  127) == 0
    ensures a % 128 == 0


/*********************** Lemmas for usb_tds_ops_impl.vad ********************/
lemma Lemma_usbtd_get_td_vaddr_result_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_USBTD_MAP_MEM())
    requires 0 <= slot < USB_TD_ENTRY_NUM
    requires tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
}

lemma Lemma_usbtd_get_td_pid_result_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_USBTD_MAP_MEM())
    requires 0 <= slot < USB_TD_ENTRY_NUM
    requires tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset);
}

lemma Lemma_usbtd_get_td_type_result_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_USBTD_MAP_MEM())
    requires 0 <= slot < USB_TD_ENTRY_NUM
    requires tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset);
}

lemma Lemma_usbtd_get_wimpdrv_slotid_result_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_USBTD_MAP_MEM())
    requires 0 <= slot < USB_TD_ENTRY_NUM
    requires tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset);
}

lemma Lemma_usbtd_get_usbpdev_slotid_result_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_USBTD_MAP_MEM())
    requires 0 <= slot < USB_TD_ENTRY_NUM
    requires tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset);
}

lemma Lemma_usbtd_get_bus_id_result_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_USBTD_MAP_MEM())
    requires 0 <= slot < USB_TD_ENTRY_NUM
    requires tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset);
}

lemma Lemma_usbtd_get_flag_result_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_USBTD_MAP_MEM())
    requires 0 <= slot < USB_TD_ENTRY_NUM
    requires tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset);
}

lemma Lemma_usbtd_get_handle_result_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_USBTD_MAP_MEM())
    requires 0 <= slot < USB_TD_ENTRY_NUM
    requires tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset);
}

lemma Lemma_usbtd_get_inputparams_result_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_USBTD_MAP_MEM())
    requires 0 <= slot < USB_TD_ENTRY_NUM
    requires tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset ||
             tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset ||
             tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    if(tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset)
    {
        Lemma_usbtd_slot_offset_AlwaysInGUSBTDsMapsMem(slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset);
    }
    else if(tmp == slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset)
    {
        Lemma_usbtd_slot_offset_AlwaysInGUSBTDsMapsMem(slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset);
    }
    else
    {
        Lemma_usbtd_slot_offset_AlwaysInGUSBTDsMapsMem(slot, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);
    }
    
    // Prove slot * G_USBTDs_MAP_ENTRY_SZ >= 0
    lemma_MulSign(slot, G_USBTDs_MAP_ENTRY_SZ);
    assert slot * G_USBTDs_MAP_ENTRY_SZ >= 0;

    // Prove is_valid_vaddr(base + tmp)
    assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);
    assert G_USBTDs_MAP_ENTRY_SZ * slot == WordAlignedMul(G_USBTDs_MAP_ENTRY_SZ, slot);
    assert WordAligned(slot * G_USBTDs_MAP_ENTRY_SZ);
}