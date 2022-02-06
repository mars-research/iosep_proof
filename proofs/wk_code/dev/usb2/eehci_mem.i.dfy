include "eehci.s.dfy"
include "../../partition_id.i.dfy"
include "ffi/usb_tds.ffi.s.dfy"
include "usb_tds_ops/usb_tds_checks.s.dfy"
include "eehci_mem_nlarith.i.dfy"
include "usb_tds_ops/usb_tds_checks.i.dfy"

/*********************** Lemma for <g_eehci_info> Modification  ********************/
// Lemma: When updating the reserved field of eEHCI Info (the eEHCI does not ref any USB TD), the result global variable 
// must satisfy  WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIINFOUpdateReservedField(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, field_vaddr:vaddr, new_v:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
        // Requirement: <eehci_slot> is valid
    requires field_vaddr == AddressOfGlobal(G_EEHCIs_Info()) + eehci_slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_Info_ENTRY_Reserved_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCIs_Info(), field_vaddr)

    requires EECHI_DoNotRefAnyUSBTD(old_globals, eehci_slot)
            // Requirement: When changing the eehci_slot information, the eehci must not reference any USB TDs

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCIs_Info(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    Lemma_P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsHaveExpectedFlags_HoldIfUSBTDRegsAndRefedUSBTDSlotsAreUnchanged(old_globals, new_globals);
    Lemma_P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI_HoldIfEEHCIIDsAndUSBTDRegsAndRefedUSBTDSlotsAreUnchanged(old_globals, new_globals);
}

// Lemma: When updating the PID field of eEHCI Info (the eEHCI does not ref any USB TD), the result global variable must  
// satisfy WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIINFOUpdatePIDField(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, field_vaddr:vaddr, new_v:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
        // Requirement: <eehci_slot> is valid
    requires field_vaddr == AddressOfGlobal(G_EEHCIs_Info()) + eehci_slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_INFO_ENTRY_PID_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCIs_Info(), field_vaddr)

    requires EECHI_DoNotRefAnyUSBTD(old_globals, eehci_slot)
            // Requirement: When changing the eehci_slot information, the eehci must not reference any USB TDs

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCIs_Info(), field_vaddr, new_v)
    requires eehci_mem_get_eehci_id(old_globals, eehci_slot) == eEHCI_ID_INVALID ==> new_v == PID_INVALID
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    Lemma_P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsHaveExpectedFlags_HoldIfUSBTDRegsAndRefedUSBTDSlotsAreUnchanged(old_globals, new_globals);
    Lemma_P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI_HoldIfEEHCIIDsAndUSBTDRegsAndRefedUSBTDSlotsAreUnchanged(old_globals, new_globals);
}

// Lemma: When updating the reserved field of eEHCI Info (the eEHCI does not ref any USB TD), and eEHCI does not ref USB 
// TDs before, then it is so now
lemma Lemma_EEHCIDoNotRefUSBTDs_IfSoBeforeAndGEEHCIINFOUpdateReservedField(
    old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, field_vaddr:vaddr, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
        // Requirement: <eehci_slot> is valid
    requires field_vaddr == AddressOfGlobal(G_EEHCIs_Info()) + eehci_slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_Info_ENTRY_Reserved_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCIs_Info(), field_vaddr)

    requires EECHI_DoNotRefAnyUSBTD(old_globals, eehci_slot)
            // Requirement: When changing the eehci_slot information, the eehci must not reference any USB TDs

    requires new_globals == global_write_word(old_globals, G_EEHCIs_Info(), field_vaddr, new_v)
    
    ensures EECHI_DoNotRefAnyUSBTD(new_globals, eehci_slot)
{
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    forall usbtd_reg_id:int | (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
        ensures eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id) == USBTD_SlotID_INVALID
    {
        assert eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id);
    }
}

// Lemma: When updating the reserved field of eEHCI Info (the eEHCI does not ref any USB TD), the result global variable   
// must satisfy WK_USBTD_Map_SecureGlobalVarValues
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfGEEHCIINFOUpdateReservedField(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, field_vaddr:vaddr, new_v:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(old_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(old_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(new_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(new_globals)

    requires eehci_valid_slot_id(eehci_slot)
        // Requirement: <eehci_slot> is valid
    requires field_vaddr == AddressOfGlobal(G_EEHCIs_Info()) + eehci_slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_Info_ENTRY_Reserved_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCIs_Info(), field_vaddr)

    requires WK_USBTD_Map_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCIs_Info(), field_vaddr, new_v)
    
    ensures WK_USBTD_Map_SecureGlobalVarValues(new_globals)
{
    Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(old_globals, new_globals);
}

// Lemma: When updating the PID field of eEHCI Info (the eEHCI does not ref any USB TD), the result global variable must  
// satisfy WK_USBTD_Map_SecureGlobalVarValues
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfGEEHCIINFOUpdatePIDField(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, field_vaddr:vaddr, new_v:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(old_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(old_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(new_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(new_globals)

    requires eehci_valid_slot_id(eehci_slot)
        // Requirement: <eehci_slot> is valid
    requires field_vaddr == AddressOfGlobal(G_EEHCIs_Info()) + eehci_slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_INFO_ENTRY_PID_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCIs_Info(), field_vaddr)

    requires WK_USBTD_Map_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCIs_Info(), field_vaddr, new_v)
    
    ensures WK_USBTD_Map_SecureGlobalVarValues(new_globals)
{
    Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(old_globals, new_globals);
}




/*********************** Lemma for <g_eehci_mem> Modification  ********************/
// Lemma: When updating the config register of eEHCI, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteEEHCIConfig(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, field_vaddr:vaddr, new_v:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
        // Requirement: <eehci_slot> is valid
    requires field_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), field_vaddr)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    forall eehci_slot, usbtd_reg_id | eehci_valid_slot_id(eehci_slot) &&  0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ensures eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id)
    {
        // Dafny can automatically prove this lemma
    }
}

// Lemma: When updating the status register of eEHCI, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteEEHCIStatus(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, field_vaddr:vaddr, new_v:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
        // Requirement: <eehci_slot> is valid
    requires field_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), field_vaddr)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    forall eehci_slot, usbtd_reg_id | eehci_valid_slot_id(eehci_slot) &&  0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ensures eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id)
    {
        // Dafny can automatically prove this lemma
    }
}

// Lemma: When updating the <intr_enable> register of eEHCI, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteEEHCIIntrEnable(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, field_vaddr:vaddr, new_v:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
        // Requirement: <eehci_slot> is valid
    requires field_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), field_vaddr)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), field_vaddr, new_v)
    requires new_v == eEHCI_Intr_Disable
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    forall eehci_slot, usbtd_reg_id | eehci_valid_slot_id(eehci_slot) &&  0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ensures eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id)
    {
        // Dafny can automatically prove this lemma
    }
}

// Lemma: When updating the <intr_target> register of eEHCI, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteEEHCIIntrTarget(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, field_vaddr:vaddr, new_v:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
        // Requirement: <eehci_slot> is valid
    requires field_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), field_vaddr)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    forall eehci_slot, usbtd_reg_id | eehci_valid_slot_id(eehci_slot) &&  0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ensures eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id)
    {
        // Dafny can automatically prove this lemma
    }
}

// Lemma: When updating the USBTD_Reg register of eEHCI, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteUSBTDReg(
    old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, usbtd_reg_id:uint32, field_vaddr:vaddr, new_usbtd_slot_id:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
    requires 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        // Requirement: <eehci_slot> and <usbtd_reg_id> are valid
    requires field_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), field_vaddr)

    requires eehci_is_active_wimp_eehci(old_globals, eehci_slot)
    requires new_usbtd_slot_id == USBTD_SlotID_INVALID || usbtd_map_valid_slot_id(new_usbtd_slot_id)
    requires usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> (
            var usbtd_idword := usbtd_map_get_idword(old_globals, new_usbtd_slot_id);
            usbtd_idword != USBTD_ID_INVALID
        )
        // Requirement: The USB TD ID of newly refed USB TD is good
    requires usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> (
            var usbtd_flags := usbtd_map_get_flags(old_globals, new_usbtd_slot_id);
            usbtd_flags == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
        )
        // Requirement: The flags of newly refed USB TD is good
    requires usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> (
            var eehci_pid := eehci_info_get_pid(old_globals, eehci_slot);
            var usbtd_pid := usbtd_map_get_pid(old_globals, new_usbtd_slot_id);
            eehci_pid == usbtd_pid
        )
        // Requirement: The PID of newly refed USB TD is good
    requires usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> (
            usbtd_slot_valid_busid(old_globals, new_usbtd_slot_id)
        ) &&
        (
            var eehci_busid:uint16 := usb_parse_eehci_id(eehci_mem_get_eehci_id(old_globals, eehci_slot)).bus_id;
            var usbtd_busid:uint16 := usbtd_map_get_busid(old_globals, new_usbtd_slot_id);
            eehci_busid == usbtd_busid
        )
        // Requirement: The bus id of newly refed USB TD is good

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), field_vaddr, new_usbtd_slot_id)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    assert global_read_fullval(old_globals, G_EEHCIs_Info()) == global_read_fullval(new_globals, G_EEHCIs_Info());
    Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteUSBTDReg_DoNotImpactOtherEEHCIMem(
        old_globals, new_globals, eehci_slot, usbtd_reg_id, field_vaddr, new_usbtd_slot_id);

    // Prove properties of the modifying eEHCI
    Lemma_WK_EEHCI_Mem_SecureGlobalVarValues_HoldIfWriteUSBTDReg_ModifyingEEHCI_ProveRefedTDsHaveValidIDWords(
        old_globals, new_globals, eehci_slot, usbtd_reg_id, field_vaddr, new_usbtd_slot_id);
    Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteUSBTDReg_ModifyingEEHCI_ProveRefedTDsHaveExpectedFlags(
        old_globals, new_globals, eehci_slot, usbtd_reg_id, field_vaddr, new_usbtd_slot_id);
    Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteUSBTDReg_ModifyingEEHCI_ProveEEHCIAndRefedTDsSamePID(
        old_globals, new_globals, eehci_slot, usbtd_reg_id, field_vaddr, new_usbtd_slot_id);
    Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteUSBTDReg_ModifyingEEHCI_ProveRefedTDsTargetUSBBusOfEEHCI(
        old_globals, new_globals, eehci_slot, usbtd_reg_id, field_vaddr, new_usbtd_slot_id);

    assert P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveValidIDWords(new_globals, eehci_slot);

    forall i | eehci_valid_slot_id(i) && !eehci_is_active_wimp_eehci(new_globals, i)
        ensures EECHI_DoNotRefAnyUSBTD(new_globals, i)
    {
        forall usbtd_reg_id:int | (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
            ensures eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id) == USBTD_SlotID_INVALID
        {
            assert eehci_mem_get_usbtd_reg(old_globals, i, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id);
        }
    }
}

lemma Lemma_eehci_mem_id_location_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_EEHCI_MEM())
    requires 0 <= slot < eEHCI_INSTANCE_NUM
    requires tmp == slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_EEHCI_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_eehci_slot_offset_AlwaysInGEEHCIMem(slot, G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset);

    // Prove slot * eEHCI_INSTANCE_BYTES >= 0
    lemma_MulSign(slot, eEHCI_INSTANCE_BYTES);
    assert slot * eEHCI_INSTANCE_BYTES >= 0;

    // Prove is_valid_vaddr(base + tmp)
    assert isUInt32(slot * eEHCI_INSTANCE_BYTES);
    assert eEHCI_INSTANCE_BYTES * slot == WordAlignedMul(eEHCI_INSTANCE_BYTES, slot);
    assert WordAligned(slot * eEHCI_INSTANCE_BYTES);
}

lemma Lemma_eehci_mem_config_location_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_EEHCI_MEM())
    requires 0 <= slot < eEHCI_INSTANCE_NUM
    requires tmp == slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_EEHCI_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_eehci_slot_offset_AlwaysInGEEHCIMem(slot, G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset);

    // Prove slot * eEHCI_INSTANCE_BYTES >= 0
    lemma_MulSign(slot, eEHCI_INSTANCE_BYTES);
    assert slot * eEHCI_INSTANCE_BYTES >= 0;

    // Prove is_valid_vaddr(base + tmp)
    assert isUInt32(slot * eEHCI_INSTANCE_BYTES);
    assert eEHCI_INSTANCE_BYTES * slot == WordAlignedMul(eEHCI_INSTANCE_BYTES, slot);
    assert WordAligned(slot * eEHCI_INSTANCE_BYTES);
}

lemma Lemma_eehci_mem_status_location_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_EEHCI_MEM())
    requires 0 <= slot < eEHCI_INSTANCE_NUM
    requires tmp == slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_EEHCI_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_eehci_slot_offset_AlwaysInGEEHCIMem(slot, G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset);

    // Prove slot * eEHCI_INSTANCE_BYTES >= 0
    lemma_MulSign(slot, eEHCI_INSTANCE_BYTES);
    assert slot * eEHCI_INSTANCE_BYTES >= 0;

    // Prove is_valid_vaddr(base + tmp)
    assert isUInt32(slot * eEHCI_INSTANCE_BYTES);
    assert eEHCI_INSTANCE_BYTES * slot == WordAlignedMul(eEHCI_INSTANCE_BYTES, slot);
    assert WordAligned(slot * eEHCI_INSTANCE_BYTES);
}

lemma Lemma_eehci_mem_intrenable_location_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_EEHCI_MEM())
    requires 0 <= slot < eEHCI_INSTANCE_NUM
    requires tmp == slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_EEHCI_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_eehci_slot_offset_AlwaysInGEEHCIMem(slot, G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset);

    // Prove slot * eEHCI_INSTANCE_BYTES >= 0
    lemma_MulSign(slot, eEHCI_INSTANCE_BYTES);
    assert slot * eEHCI_INSTANCE_BYTES >= 0;

    // Prove is_valid_vaddr(base + tmp)
    assert isUInt32(slot * eEHCI_INSTANCE_BYTES);
    assert eEHCI_INSTANCE_BYTES * slot == WordAlignedMul(eEHCI_INSTANCE_BYTES, slot);
    assert WordAligned(slot * eEHCI_INSTANCE_BYTES);
}

lemma Lemma_eehci_mem_intrtarget_location_is_gvar_valid_addr(base:vaddr, slot:uint32, tmp:int)
    requires base == AddressOfGlobal(G_EEHCI_MEM())
    requires 0 <= slot < eEHCI_INSTANCE_NUM
    requires tmp == slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset

    ensures is_valid_addr(base + tmp)
    ensures is_valid_vaddr(base + tmp)
    ensures is_gvar_valid_vaddr(G_EEHCI_MEM(), base + tmp)
{
    lemma_DistinctGlobals();

    Lemma_eehci_slot_offset_AlwaysInGEEHCIMem(slot, G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset);

    // Prove slot * eEHCI_INSTANCE_BYTES >= 0
    lemma_MulSign(slot, eEHCI_INSTANCE_BYTES);
    assert slot * eEHCI_INSTANCE_BYTES >= 0;

    // Prove is_valid_vaddr(base + tmp)
    assert isUInt32(slot * eEHCI_INSTANCE_BYTES);
    assert eEHCI_INSTANCE_BYTES * slot == WordAlignedMul(eEHCI_INSTANCE_BYTES, slot);
    assert WordAligned(slot * eEHCI_INSTANCE_BYTES);
}

lemma Lemma_eehci_slot_offset_in_content_AlwaysValidGEEHCIMemAddr(slot:uint32)
    requires eehci_valid_slot_id(slot)

    ensures var td_addr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset;
                is_gvar_valid_addr(G_EEHCI_MEM(), td_addr) && is_gvar_valid_vaddr(G_EEHCI_MEM(), td_addr)
    ensures var td_addr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset;
            forall i:int :: 0 <= i < eEHCI_USBTD_SlotID_NUMS
                ==> is_gvar_valid_addr(G_EEHCI_MEM(), td_addr + i * UINT32_BYTES) &&
                    is_gvar_valid_vaddr(G_EEHCI_MEM(), td_addr + i * UINT32_BYTES)
{
    var td_addr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset;
    forall i:int | 0 <= i < eEHCI_USBTD_SlotID_NUMS
        ensures is_gvar_valid_addr(G_EEHCI_MEM(), td_addr + i * UINT32_BYTES)
        ensures is_gvar_valid_vaddr(G_EEHCI_MEM(), td_addr + i * UINT32_BYTES)
    {
        Lemma_eehci_slot_offset_AlwaysValidGEEHCIMemAddr(slot, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + i * UINT32_BYTES);
    }

    assert is_gvar_valid_addr(G_EEHCI_MEM(), td_addr + 0 * UINT32_BYTES);
    assert is_gvar_valid_vaddr(G_EEHCI_MEM(), td_addr + 0 * UINT32_BYTES);
}

lemma Lemma_WK_EEHCI_Mem_PreserveIDFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires eehci_valid_slot_id(slot)
    requires 0 <= offset < eEHCI_INSTANCE_BYTES
    requires offset != G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset
    requires var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + offset;
            is_gvar_valid_addr(G_EEHCI_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_EEHCI_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < eEHCI_INSTANCE_NUM
                ==> eehci_mem_get_eehci_id(globals1, i) == eehci_mem_get_eehci_id(globals2, i)
{
    forall i | 0 <= i < eEHCI_INSTANCE_NUM
        ensures eehci_mem_get_eehci_id(globals1, i) == eehci_mem_get_eehci_id(globals2, i)
    {
        var v_offset := i * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;

        // Prove ValidGlobalOffset(G_EEHCI_MEM(), v_offset)
        Lemma_eehci_mem_id_location_is_gvar_valid_addr(AddressOfGlobal(G_EEHCI_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_EEHCI_MEM(), v_offset);

        // Prove v_offset != slot * eEHCI_INSTANCE_BYTES + offset;
        if(v_offset == slot * eEHCI_INSTANCE_BYTES + offset)
        {
            assert 0 - eEHCI_INSTANCE_BYTES < offset - G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset < eEHCI_INSTANCE_BYTES;
            assert slot != i;

            assert offset - G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset == i * eEHCI_INSTANCE_BYTES - slot * eEHCI_INSTANCE_BYTES;
            lemma_MulDistrib_Sub(i, slot, eEHCI_INSTANCE_BYTES);
            assert offset - G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset == (i - slot) * eEHCI_INSTANCE_BYTES;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset >= eEHCI_INSTANCE_BYTES;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset <= -1 * eEHCI_INSTANCE_BYTES;
                Lemma_IntMul_EqualityOfMinusN(eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset <= 0 - eEHCI_INSTANCE_BYTES;
            }
            assert false;
        }
        assert v_offset != slot * eEHCI_INSTANCE_BYTES + offset;
    }
}

lemma Lemma_WK_EEHCI_Mem_PreserveConfigFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires eehci_valid_slot_id(slot)
    requires 0 <= offset < eEHCI_INSTANCE_BYTES
    requires offset != G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset
    requires var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + offset;
            is_gvar_valid_addr(G_EEHCI_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_EEHCI_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < eEHCI_INSTANCE_NUM
                ==> eehci_mem_get_config_reg(globals1, i) == eehci_mem_get_config_reg(globals2, i)
{
    forall i | 0 <= i < eEHCI_INSTANCE_NUM
        ensures eehci_mem_get_config_reg(globals1, i) == eehci_mem_get_config_reg(globals2, i)
    {
        var v_offset := i * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset;

        // Prove ValidGlobalOffset(G_EEHCI_MEM(), v_offset)
        Lemma_eehci_mem_config_location_is_gvar_valid_addr(AddressOfGlobal(G_EEHCI_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_EEHCI_MEM(), v_offset);

        // Prove v_offset != slot * eEHCI_INSTANCE_BYTES + offset;
        if(v_offset == slot * eEHCI_INSTANCE_BYTES + offset)
        {
            assert 0 - eEHCI_INSTANCE_BYTES < offset - G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset < eEHCI_INSTANCE_BYTES;
            assert slot != i;

            assert offset - G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset == i * eEHCI_INSTANCE_BYTES - slot * eEHCI_INSTANCE_BYTES;
            lemma_MulDistrib_Sub(i, slot, eEHCI_INSTANCE_BYTES);
            assert offset - G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset == (i - slot) * eEHCI_INSTANCE_BYTES;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset >= eEHCI_INSTANCE_BYTES;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset <= -1 * eEHCI_INSTANCE_BYTES;
                Lemma_IntMul_EqualityOfMinusN(eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset <= 0 - eEHCI_INSTANCE_BYTES;
            }
            assert false;
        }
        assert v_offset != slot * eEHCI_INSTANCE_BYTES + offset;
    }
}

lemma Lemma_WK_EEHCI_Mem_PreserveStatusFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires eehci_valid_slot_id(slot)
    requires 0 <= offset < eEHCI_INSTANCE_BYTES
    requires offset != G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset
    requires var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + offset;
            is_gvar_valid_addr(G_EEHCI_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_EEHCI_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < eEHCI_INSTANCE_NUM
                ==> eehci_mem_get_status_reg(globals1, i) == eehci_mem_get_status_reg(globals2, i)
{
    forall i | 0 <= i < eEHCI_INSTANCE_NUM
        ensures eehci_mem_get_status_reg(globals1, i) == eehci_mem_get_status_reg(globals2, i)
    {
        var v_offset := i * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset;

        // Prove ValidGlobalOffset(G_EEHCI_MEM(), v_offset)
        Lemma_eehci_mem_status_location_is_gvar_valid_addr(AddressOfGlobal(G_EEHCI_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_EEHCI_MEM(), v_offset);

        // Prove v_offset != slot * eEHCI_INSTANCE_BYTES + offset;
        if(v_offset == slot * eEHCI_INSTANCE_BYTES + offset)
        {
            assert 0 - eEHCI_INSTANCE_BYTES < offset - G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset < eEHCI_INSTANCE_BYTES;
            assert slot != i;

            assert offset - G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset == i * eEHCI_INSTANCE_BYTES - slot * eEHCI_INSTANCE_BYTES;
            lemma_MulDistrib_Sub(i, slot, eEHCI_INSTANCE_BYTES);
            assert offset - G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset == (i - slot) * eEHCI_INSTANCE_BYTES;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset >= eEHCI_INSTANCE_BYTES;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset <= -1 * eEHCI_INSTANCE_BYTES;
                Lemma_IntMul_EqualityOfMinusN(eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset <= 0 - eEHCI_INSTANCE_BYTES;
            }
            assert false;
        }
        assert v_offset != slot * eEHCI_INSTANCE_BYTES + offset;
    }
}

lemma Lemma_WK_EEHCI_Mem_PreserveIntrEnableFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires eehci_valid_slot_id(slot)
    requires 0 <= offset < eEHCI_INSTANCE_BYTES
    requires offset != G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset
    requires var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + offset;
            is_gvar_valid_addr(G_EEHCI_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_EEHCI_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < eEHCI_INSTANCE_NUM
                ==> eehci_mem_get_intr_enable_reg(globals1, i) == eehci_mem_get_intr_enable_reg(globals2, i)
{
    forall i | 0 <= i < eEHCI_INSTANCE_NUM
        ensures eehci_mem_get_intr_enable_reg(globals1, i) == eehci_mem_get_intr_enable_reg(globals2, i)
    {
        var v_offset := i * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset;

        // Prove ValidGlobalOffset(G_EEHCI_MEM(), v_offset)
        Lemma_eehci_mem_intrenable_location_is_gvar_valid_addr(AddressOfGlobal(G_EEHCI_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_EEHCI_MEM(), v_offset);

        // Prove v_offset != slot * eEHCI_INSTANCE_BYTES + offset;
        if(v_offset == slot * eEHCI_INSTANCE_BYTES + offset)
        {
            assert 0 - eEHCI_INSTANCE_BYTES < offset - G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset < eEHCI_INSTANCE_BYTES;
            assert slot != i;

            assert offset - G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset == i * eEHCI_INSTANCE_BYTES - slot * eEHCI_INSTANCE_BYTES;
            lemma_MulDistrib_Sub(i, slot, eEHCI_INSTANCE_BYTES);
            assert offset - G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset == (i - slot) * eEHCI_INSTANCE_BYTES;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset >= eEHCI_INSTANCE_BYTES;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset <= -1 * eEHCI_INSTANCE_BYTES;
                Lemma_IntMul_EqualityOfMinusN(eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset <= 0 - eEHCI_INSTANCE_BYTES;
            }
            assert false;
        }
        assert v_offset != slot * eEHCI_INSTANCE_BYTES + offset;
    }
}

lemma Lemma_WK_EEHCI_Mem_PreserveIntrTargetFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires eehci_valid_slot_id(slot)
    requires 0 <= offset < eEHCI_INSTANCE_BYTES
    requires offset != G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset
    requires var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + offset;
            is_gvar_valid_addr(G_EEHCI_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_EEHCI_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < eEHCI_INSTANCE_NUM
                ==> eehci_mem_get_intr_target_reg(globals1, i) == eehci_mem_get_intr_target_reg(globals2, i)
{
    forall i | 0 <= i < eEHCI_INSTANCE_NUM
        ensures eehci_mem_get_intr_target_reg(globals1, i) == eehci_mem_get_intr_target_reg(globals2, i)
    {
        var v_offset := i * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset;

        // Prove ValidGlobalOffset(G_EEHCI_MEM(), v_offset)
        Lemma_eehci_mem_intrtarget_location_is_gvar_valid_addr(AddressOfGlobal(G_EEHCI_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_EEHCI_MEM(), v_offset);

        // Prove v_offset != slot * eEHCI_INSTANCE_BYTES + offset;
        if(v_offset == slot * eEHCI_INSTANCE_BYTES + offset)
        {
            assert 0 - eEHCI_INSTANCE_BYTES < offset - G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset < eEHCI_INSTANCE_BYTES;
            assert slot != i;

            assert offset - G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset == i * eEHCI_INSTANCE_BYTES - slot * eEHCI_INSTANCE_BYTES;
            lemma_MulDistrib_Sub(i, slot, eEHCI_INSTANCE_BYTES);
            assert offset - G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset == (i - slot) * eEHCI_INSTANCE_BYTES;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset >= eEHCI_INSTANCE_BYTES;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset <= -1 * eEHCI_INSTANCE_BYTES;
                Lemma_IntMul_EqualityOfMinusN(eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset <= 0 - eEHCI_INSTANCE_BYTES;
            }
            assert false;
        }
        assert v_offset != slot * eEHCI_INSTANCE_BYTES + offset;
    }
}

lemma Lemma_WK_EEHCI_Mem_PreserveUSBTDRegsIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires eehci_valid_slot_id(slot)
    requires (offset == G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset) || (offset == G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset) || 
            (offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset) || (offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset) || 
            (offset == G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset) || (offset == G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset)
    requires var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + offset;
            is_gvar_valid_addr(G_EEHCI_MEM(), vaddr) &&
            (globals2 == global_write_word(globals1, G_EEHCI_MEM(), vaddr, new_v) ||
            globals2 == global_write_at_vaddr32(globals1, G_EEHCI_MEM(), vaddr, new_v))

    ensures forall i :: 0 <= i < eEHCI_INSTANCE_NUM
                ==> p_eehci_mem_usbtd_regs_equal(globals1, globals2, i)
{
    reveal p_eehci_mem_usbtd_regs_equal();

    forall i | 0 <= i < eEHCI_INSTANCE_NUM
        ensures p_eehci_mem_usbtd_regs_equal(globals1, globals2, i)
    {
        forall j | 0 <= j < eEHCI_USBTD_SlotID_NUMS
            ensures var td_addr := AddressOfGlobal(G_EEHCI_MEM()) + i * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset;
                    is_gvar_valid_addr(G_EEHCI_MEM(), td_addr + j * UINT32_BYTES) &&
                    global_read_word(globals1, G_EEHCI_MEM(), td_addr + j * UINT32_BYTES) == global_read_word(globals2, G_EEHCI_MEM(), td_addr + j * UINT32_BYTES)
        {
            var td_addr := AddressOfGlobal(G_EEHCI_MEM()) + i * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset;

            var v_offset := i * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + j * UINT32_BYTES;

            // Prove ValidGlobalOffset(G_EEHCI_MEM(), v_offset)
            Lemma_eehci_slot_offset_AlwaysValidGEEHCIMemAddr(i, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + j * UINT32_BYTES);
            assert ValidGlobalOffset(G_EEHCI_MEM(), v_offset);

            // Prove v_offset != slot * eEHCI_INSTANCE_BYTES + offset;
            if(v_offset == slot * eEHCI_INSTANCE_BYTES + offset)
            {
                assert 0 - eEHCI_INSTANCE_BYTES < offset - G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset - j * UINT32_BYTES < eEHCI_INSTANCE_BYTES;
                assert slot != i;

                assert offset - G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset - j * UINT32_BYTES == i * eEHCI_INSTANCE_BYTES - slot * eEHCI_INSTANCE_BYTES;
                lemma_MulDistrib_Sub(i, slot, eEHCI_INSTANCE_BYTES);
                assert offset - G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset - j * UINT32_BYTES == (i - slot) * eEHCI_INSTANCE_BYTES;

                // Show conflict
                if(i > slot)
                {
                    assert i - slot >= 1;
                    Lemma_NatMul_Ineq(1, i - slot, eEHCI_INSTANCE_BYTES);
                    assert offset - G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset - j * UINT32_BYTES >= eEHCI_INSTANCE_BYTES;
                }
                else
                {
                    assert i < slot;
                    assert i - slot <= -1;
                    Lemma_IntMul_Ineq(i - slot, -1, eEHCI_INSTANCE_BYTES);
                    assert offset - G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset - j * UINT32_BYTES <= -1 * eEHCI_INSTANCE_BYTES;
                    Lemma_IntMul_EqualityOfMinusN(eEHCI_INSTANCE_BYTES);
                    assert offset - G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset - j * UINT32_BYTES <= 0 - eEHCI_INSTANCE_BYTES;
                }
                assert false;
            }
            assert v_offset != slot * eEHCI_INSTANCE_BYTES + offset; 
        }
    }
}

// Lemma: When modifying one eEHCI slot, other eEHCI slots are unmodified
lemma Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires eehci_valid_slot_id(slot)
    requires 0 <= offset < eEHCI_INSTANCE_BYTES
    requires var vaddr := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + offset;
            is_gvar_valid_addr(G_EEHCI_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_EEHCI_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < eEHCI_INSTANCE_NUM && i != slot
                ==> p_eehci_mem_equal(globals1, globals2, i)
{
    reveal p_eehci_mem_equal();
    reveal p_eehci_mem_usbtd_regs_equal();

    forall i | 0 <= i < eEHCI_INSTANCE_NUM && i != slot
        ensures p_eehci_mem_equal(globals1, globals2, i)
    {
        Lemma_eehci_slot_offset_AlwaysValidGEEHCIMemAddr(i, G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset);        
        if(eehci_mem_get_eehci_id(globals1, i) != eehci_mem_get_eehci_id(globals2, i))
        {
            var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + i * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
            assert global_read_word(globals1, G_EEHCI_MEM(), vaddr1) != global_read_word(globals2, G_EEHCI_MEM(), vaddr1);
            assert i * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset == slot * eEHCI_INSTANCE_BYTES + offset;
            Lemma_eehci_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset, slot, offset);
            assert false;
        }
        assert eehci_mem_get_eehci_id(globals1, i) == eehci_mem_get_eehci_id(globals2, i);

        Lemma_eehci_slot_offset_AlwaysValidGEEHCIMemAddr(i, G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset);        
        if(eehci_mem_get_handle_reg(globals1, i) != eehci_mem_get_handle_reg(globals2, i))
        {
            var vaddr1 := AddressOfGlobal(G_EEHCI_MEM()) + i * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset;
            assert global_read_word(globals1, G_EEHCI_MEM(), vaddr1) != global_read_word(globals2, G_EEHCI_MEM(), vaddr1);
            assert i * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset == slot * eEHCI_INSTANCE_BYTES + offset;
            Lemma_eehci_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset, slot, offset);
            assert false;
        }
        assert eehci_mem_get_handle_reg(globals1, i) == eehci_mem_get_handle_reg(globals2, i);
        assert eehci_mem_get_config_reg(globals1, i) == eehci_mem_get_config_reg(globals2, i);
        assert eehci_mem_get_status_reg(globals1, i) == eehci_mem_get_status_reg(globals2, i);
        
        assert eehci_mem_get_intr_enable_reg(globals1, i) == eehci_mem_get_intr_enable_reg(globals2, i);
        assert eehci_mem_get_intr_target_reg(globals1, i) == eehci_mem_get_intr_target_reg(globals2, i);


        assert p_eehci_mem_usbtd_regs_equal(globals1, globals2, i);
    }
}

// Predicate: <ffi_eehci_activate> modify the given eEHCI slot only
predicate p_ffi_eehci_activate_modify_gvars_one_eEHCIslot_only(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires eehci_valid_slot_id(eehci_slot)
        // Requirement: <eehci_slot> is valid
{
    // Other eEHCI mem slots are unchanged
    (forall i :: (eehci_valid_slot_id(i) && i != eehci_slot) ==> p_eehci_mem_equal(old_globals, new_globals, i)) &&

    // Other global variables are unchanged
    globals_other_gvar_unchanged(old_globals, new_globals, G_EEHCI_MEM())
}

// Lemma: Transitivity of p_eehci_mem_equal
lemma Lemma_p_eehci_mem_slot_equal_transitive(globals1:globalsmap, globals2:globalsmap, globals3:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(globals3)

    requires eehci_valid_slot_id(slot)

    ensures  p_eehci_mem_equal(globals1, globals2, slot) && p_eehci_mem_equal(globals2, globals3, slot)
                ==> p_eehci_mem_equal(globals1, globals3, slot)
{
    reveal p_eehci_mem_equal();
    reveal p_eehci_mem_usbtd_regs_equal();
}

// Lemma: Transitivity of p_eehci_mem_usbtd_regs_equal
lemma Lemma_p_eehci_mem_usbtd_regs_equal_transitive(globals1:globalsmap, globals2:globalsmap, globals3:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(globals3)

    requires eehci_valid_slot_id(slot)

    ensures  p_eehci_mem_usbtd_regs_equal(globals1, globals2, slot) && p_eehci_mem_usbtd_regs_equal(globals2, globals3, slot)
                ==> p_eehci_mem_usbtd_regs_equal(globals1, globals3, slot)
{
    reveal p_eehci_mem_usbtd_regs_equal();
}

// Lemma: When updating the reserved field of eEHCI Info (the eEHCI does not ref any USB TD), the result global variable   
// must satisfy WK_USBTD_Map_SecureGlobalVarValues
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfGEEHCIMemUpdateStatus(old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, field_vaddr:vaddr, new_v:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(old_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(old_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(new_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(new_globals)

    requires eehci_valid_slot_id(eehci_slot)
        // Requirement: <eehci_slot> is valid
    requires field_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), field_vaddr)

    requires WK_USBTD_Map_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), field_vaddr, new_v)
    
    ensures WK_USBTD_Map_SecureGlobalVarValues(new_globals)
{
    Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(old_globals, new_globals);
}




/*********************** Lemma for eEHCI Activation and Deactivation  ********************/
// Lemma: When activating an eEHCI, the result global variable must satisfy WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfEEHCIActivate(
    old_globals:globalsmap, new_globals:globalsmap, new_eehci_slot:uint32, eehci_id_vaddr:vaddr, new_id:word, eehci_handle_vaddr:vaddr, new_handle:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(new_eehci_slot)
        // Requirement: <new_eehci_slot> is valid
    requires eehci_id_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), eehci_id_vaddr)
    requires eehci_handle_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), eehci_handle_vaddr)

    requires forall i:word :: eehci_valid_slot_id(i)
                ==> eehci_mem_get_eehci_id(old_globals, i) != new_id
        // Requirement: <eehci_id> must be unique in <g_eehci_mem>
    requires new_id != eEHCI_ID_INVALID
        // Requirement: <new_id> is not eEHCI_ID_INVALID

    requires var new_globals1 := global_write_word(old_globals, G_EEHCI_MEM(), eehci_id_vaddr, new_id);
             var new_globals2 := global_write_word(new_globals1, G_EEHCI_MEM(), eehci_handle_vaddr, new_handle);
             eehci_mem_cleared_all_regs(new_globals2, new_globals, new_eehci_slot)
        // Requirement: Only <eehci_id>, <eehci_handle> and <USBTD_regs> fields of the given eEHCI slot is modified

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)

    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
{
    reveal eehci_mem_cleared_all_regs();

    assert global_read_fullval(old_globals, G_EEHCIs_Info()) == global_read_fullval(new_globals, G_EEHCIs_Info());
    forall i | eehci_valid_slot_id(i) && !eehci_is_active_wimp_eehci(new_globals, i)
        ensures EECHI_DoNotRefAnyUSBTD(new_globals, i)
    {
        if(i != new_eehci_slot)
        {
            forall usbtd_reg_id:int | (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
                ensures eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id) == USBTD_SlotID_INVALID
            {
                assert eehci_mem_get_usbtd_reg(old_globals, i, usbtd_reg_id) == USBTD_SlotID_INVALID;
                assert eehci_mem_get_usbtd_reg(old_globals, i, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id);
            }
        }
        else
        {
            assert EECHI_DoNotRefAnyUSBTD(new_globals, i);
        }
    }

    forall i | eehci_valid_slot_id(i)
        ensures P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(new_globals, i)
    {
        if(i != new_eehci_slot)
        {
            assert forall usbtd_reg_id:int :: (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
                    ==> eehci_mem_get_usbtd_reg(old_globals, i, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id);

            assert P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(new_globals, i);
        }
        else
        {
            assert P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(new_globals, i);
        }
    }
}

// Lemma: When activating an eEHCI, the result global variable must satisfy WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfEEHCIActivate(
    old_globals:globalsmap, new_globals:globalsmap, new_eehci_slot:uint32, eehci_id_vaddr:vaddr, new_id:word, eehci_handle_vaddr:vaddr, new_handle:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(new_eehci_slot)
        // Requirement: <new_eehci_slot> is valid
    requires eehci_id_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), eehci_id_vaddr)
    requires eehci_handle_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + new_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), eehci_handle_vaddr)

    requires forall i:word :: eehci_valid_slot_id(i)
                ==> eehci_mem_get_eehci_id(old_globals, i) != new_id
        // Requirement: <eehci_id> must be unique in <g_eehci_mem>
    requires new_id != eEHCI_ID_INVALID
        // Requirement: <new_id> is not eEHCI_ID_INVALID

    requires var new_globals1 := global_write_word(old_globals, G_EEHCI_MEM(), eehci_id_vaddr, new_id);
             var new_globals2 := global_write_word(new_globals1, G_EEHCI_MEM(), eehci_handle_vaddr, new_handle);
             eehci_mem_cleared_all_regs(new_globals2, new_globals, new_eehci_slot)
        // Requirement: Only <eehci_id>, <eehci_handle> and <USBTD_regs> fields of the given eEHCI slot is modified

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)

    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    reveal eehci_mem_cleared_all_regs();

    assert global_read_fullval(old_globals, G_EEHCIs_Info()) == global_read_fullval(new_globals, G_EEHCIs_Info());
    forall i | eehci_valid_slot_id(i) && !eehci_is_active_wimp_eehci(new_globals, i)
        ensures EECHI_DoNotRefAnyUSBTD(new_globals, i)
    {
        if(i != new_eehci_slot)
        {
            forall usbtd_reg_id:int | (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
                ensures eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id) == USBTD_SlotID_INVALID
            {
                assert eehci_mem_get_usbtd_reg(old_globals, i, usbtd_reg_id) == USBTD_SlotID_INVALID;
                assert eehci_mem_get_usbtd_reg(old_globals, i, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id);
            }
        }
        else
        {
            assert EECHI_DoNotRefAnyUSBTD(new_globals, i);
        }
    }

    forall i | eehci_valid_slot_id(i)
        ensures P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveValidIDWords(new_globals, i)
        ensures P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags(new_globals, i)
        ensures P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(new_globals, i)
        ensures P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(new_globals, i)
    {
        if(i != new_eehci_slot)
        {
            assert forall usbtd_reg_id:int :: (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
                    ==> eehci_mem_get_usbtd_reg(old_globals, i, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id);

            assert P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveValidIDWords(new_globals, i);
            assert P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags(new_globals, i);
            assert P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(new_globals, i);
            assert P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(new_globals, i);
        }
        else
        {
            assert P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveValidIDWords(new_globals, i);
            assert P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags(new_globals, i);
            assert P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(new_globals, i);
            assert P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(new_globals, i);
        }
    }
}

// Lemma: When deactivating an eEHCI, the result global variable must satisfy WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfEEHCIDeactivate(
    old_globals:globalsmap, new_globals:globalsmap, in_eehci_slot:uint32, eehci_id_vaddr:vaddr
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(in_eehci_slot)
        // Requirement: <in_eehci_slot> is valid
    requires EECHI_DoNotRefAnyUSBTD(old_globals, in_eehci_slot)
        // Requirement: The given eEHCI must not reference any USB TDs
    requires eehci_info_get_pid(old_globals, in_eehci_slot) == WS_PartitionID(PID_INVALID)
        // Requirement: The given eEHCI must be inactive in the I/O separation code
    requires eehci_id_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + in_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), eehci_id_vaddr)

    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), eehci_id_vaddr, eEHCI_ID_INVALID)
        // Requirement: Only <eehci_id> field of the given eEHCI slot is modified

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)

    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
{
    reveal eehci_mem_cleared_usbtd_regs();

    assert global_read_fullval(old_globals, G_EEHCIs_Info()) == global_read_fullval(new_globals, G_EEHCIs_Info());
    forall i | eehci_valid_slot_id(i) && !eehci_is_active_wimp_eehci(new_globals, i)
        ensures EECHI_DoNotRefAnyUSBTD(new_globals, i)
    {
        assert forall usbtd_reg_id:int :: (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
                    ==> eehci_mem_get_usbtd_reg(old_globals, i, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id);
    }

    forall i | eehci_valid_slot_id(i)
        ensures P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(new_globals, i)
    {
        assert forall usbtd_reg_id:int :: (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
                    ==> eehci_mem_get_usbtd_reg(old_globals, i, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id);
    }
}

// Lemma: When deactivating an eEHCI, the result global variable must satisfy WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfEEHCIDeactivate(
    old_globals:globalsmap, new_globals:globalsmap, in_eehci_slot:uint32, eehci_id_vaddr:vaddr
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(in_eehci_slot)
        // Requirement: <in_eehci_slot> is valid
    requires EECHI_DoNotRefAnyUSBTD(old_globals, in_eehci_slot)
        // Requirement: The given eEHCI must not reference any USB TDs
    requires eehci_info_get_pid(old_globals, in_eehci_slot) == WS_PartitionID(PID_INVALID)
        // Requirement: The given eEHCI must be inactive in the I/O separation code
    requires eehci_id_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + in_eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), eehci_id_vaddr)


    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), eehci_id_vaddr, eEHCI_ID_INVALID)
        // Requirement: Only <eehci_id> field of the given eEHCI slot is modified

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)

    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    reveal eehci_mem_cleared_usbtd_regs();

    assert global_read_fullval(old_globals, G_EEHCIs_Info()) == global_read_fullval(new_globals, G_EEHCIs_Info());
    forall i | eehci_valid_slot_id(i) && !eehci_is_active_wimp_eehci(new_globals, i)
        ensures EECHI_DoNotRefAnyUSBTD(new_globals, i)
    {
        assert forall usbtd_reg_id:int :: (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
                    ==> eehci_mem_get_usbtd_reg(old_globals, i, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id);
    }

    forall i | eehci_valid_slot_id(i)
        ensures P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveValidIDWords(new_globals, i)
        ensures P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags(new_globals, i)
        ensures P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(new_globals, i)
        ensures P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(new_globals, i)
    {
        assert forall usbtd_reg_id:int :: (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
                    ==> eehci_mem_get_usbtd_reg(old_globals, i, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id);
    }
}

lemma Lemma_eehci_mem_clear_usbtd_regs_PreserveOtherEEHCIMemSlots(old_globals:globalsmap, new_globals:globalsmap, eehci_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires eehci_valid_slot_id(eehci_slot_id)
    requires new_globals == eehci_mem_clear_usbtd_regs(old_globals, eehci_slot_id)

    ensures forall i :: (eehci_valid_slot_id(i) && i != eehci_slot_id) ==> p_eehci_mem_equal(old_globals, new_globals, i)
{
    var addr := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset;
    lemma_DistinctGlobals();

    var new_globals1 := global_write_at_vaddr32(old_globals, G_EEHCI_MEM(), addr, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(old_globals, new_globals1, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset, USBTD_SlotID_INVALID);
    var new_globals2 := global_write_at_vaddr32(new_globals1, G_EEHCI_MEM(), addr + 1 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals1, new_globals2, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 1 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals3 := global_write_at_vaddr32(new_globals2, G_EEHCI_MEM(), addr + 2 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals2, new_globals3, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 2 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals4 := global_write_at_vaddr32(new_globals3, G_EEHCI_MEM(), addr + 3 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals3, new_globals4, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 3 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals5 := global_write_at_vaddr32(new_globals4, G_EEHCI_MEM(), addr + 4 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals4, new_globals5, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 4 * UINT32_BYTES, USBTD_SlotID_INVALID);

    var new_globals6 := global_write_at_vaddr32(new_globals5, G_EEHCI_MEM(), addr + 5 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals5, new_globals6, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 5 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals7 := global_write_at_vaddr32(new_globals6, G_EEHCI_MEM(), addr + 6 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals6, new_globals7, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 6 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals8 := global_write_at_vaddr32(new_globals7, G_EEHCI_MEM(), addr + 7 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals7, new_globals8, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 7 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals9 := global_write_at_vaddr32(new_globals8, G_EEHCI_MEM(), addr + 8 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals8, new_globals9, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 8 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals10 := global_write_at_vaddr32(new_globals9, G_EEHCI_MEM(), addr + 9 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals9, new_globals10, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 9 * UINT32_BYTES, USBTD_SlotID_INVALID);

    var new_globals11 := global_write_at_vaddr32(new_globals10, G_EEHCI_MEM(), addr + 10 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals10, new_globals11, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 10 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals12 := global_write_at_vaddr32(new_globals11, G_EEHCI_MEM(), addr + 11 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals11, new_globals12, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 11 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals13 := global_write_at_vaddr32(new_globals12, G_EEHCI_MEM(), addr + 12 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals12, new_globals13, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 12 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals14 := global_write_at_vaddr32(new_globals13, G_EEHCI_MEM(), addr + 13 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals13, new_globals14, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 13 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals15 := global_write_at_vaddr32(new_globals14, G_EEHCI_MEM(), addr + 14 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals14, new_globals15, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 14 * UINT32_BYTES, USBTD_SlotID_INVALID);

    var new_globals16 := global_write_at_vaddr32(new_globals15, G_EEHCI_MEM(), addr + 15 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals15, new_globals16, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 15 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals17 := global_write_at_vaddr32(new_globals16, G_EEHCI_MEM(), addr + 16 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals16, new_globals17, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 16 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals18 := global_write_at_vaddr32(new_globals17, G_EEHCI_MEM(), addr + 17 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals17, new_globals18, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 17 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals19 := global_write_at_vaddr32(new_globals18, G_EEHCI_MEM(), addr + 18 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals18, new_globals19, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 18 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals20 := global_write_at_vaddr32(new_globals19, G_EEHCI_MEM(), addr + 19 * UINT32_BYTES, USBTD_SlotID_INVALID);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals19, new_globals20, eehci_slot_id, G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + 19 * UINT32_BYTES, USBTD_SlotID_INVALID);

    assert new_globals == new_globals20;

    forall i | (eehci_valid_slot_id(i) && i != eehci_slot_id) 
        ensures p_eehci_mem_equal(old_globals, new_globals, i)
    {
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals1, new_globals2, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals2, new_globals3, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals3, new_globals4, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals4, new_globals5, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals5, new_globals6, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals6, new_globals7, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals7, new_globals8, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals8, new_globals9, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals9, new_globals10, i);

        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals10, new_globals11, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals11, new_globals12, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals12, new_globals13, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals13, new_globals14, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals14, new_globals15, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals15, new_globals16, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals16, new_globals17, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals17, new_globals18, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals18, new_globals19, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals19, new_globals20, i);
    }
}

lemma Lemma_eehci_mem_clear_all_regs_PreserveOtherEEHCIMemSlots(old_globals:globalsmap, new_globals:globalsmap, eehci_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires eehci_valid_slot_id(eehci_slot_id)
    requires new_globals == eehci_mem_clear_all_regs(old_globals, eehci_slot_id)

    ensures forall i :: (eehci_valid_slot_id(i) && i != eehci_slot_id) ==> p_eehci_mem_equal(old_globals, new_globals, i)
{
    reveal p_eehci_mem_equal();
    reveal p_eehci_mem_usbtd_regs_equal();

    lemma_DistinctGlobals(); 
    var new_globals1 := eehci_mem_clear_usbtd_regs(old_globals, eehci_slot_id);
    Lemma_eehci_mem_clear_usbtd_regs_PreserveOtherEEHCIMemSlots(old_globals, new_globals1, eehci_slot_id);

    var addr2 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset;
    var new_globals2 := global_write_at_vaddr32(new_globals1, G_EEHCI_MEM(), addr2, eEHCI_Config_Disable);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals1, new_globals2, eehci_slot_id, G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset, eEHCI_Config_Disable);

    var addr3 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset;
    var new_globals3 := global_write_at_vaddr32(new_globals2, G_EEHCI_MEM(), addr3, 0);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals2, new_globals3, eehci_slot_id, G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset, 0);

    var addr4 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset;
    var new_globals4 := global_write_at_vaddr32(new_globals3, G_EEHCI_MEM(), addr4, eEHCI_Intr_Disable);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals3, new_globals4, eehci_slot_id, G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset, eEHCI_Intr_Disable);

    var addr5 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset;
    var new_globals5 := global_write_at_vaddr32(new_globals4, G_EEHCI_MEM(), addr5, 0);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals4, new_globals5, eehci_slot_id, G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset, 0);

    assert new_globals == new_globals5;

    forall i | (eehci_valid_slot_id(i) && i != eehci_slot_id) 
        ensures p_eehci_mem_equal(old_globals, new_globals, i)
    {
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals1, new_globals2, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals2, new_globals3, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals3, new_globals4, i);
        Lemma_p_eehci_mem_slot_equal_transitive(old_globals, new_globals4, new_globals5, i);
    }
}

lemma Lemma_eehci_mem_clear_all_regs_PreserveOtherGVars(old_globals:globalsmap, new_globals:globalsmap, eehci_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires eehci_valid_slot_id(eehci_slot_id)
    requires new_globals == eehci_mem_clear_all_regs(old_globals, eehci_slot_id)

    ensures forall g :: g != G_EEHCI_MEM() && is_gvar_exist(g)
                ==> global_read_fullval(old_globals, g) == global_read_fullval(new_globals, g)
{
    reveal p_eehci_mem_equal();
    reveal p_eehci_mem_usbtd_regs_equal();

    lemma_DistinctGlobals(); 
    var new_globals1 := eehci_mem_clear_usbtd_regs(old_globals, eehci_slot_id);
    Lemma_eehci_mem_clear_usbtd_regs_PreserveOtherEEHCIMemSlots(old_globals, new_globals1, eehci_slot_id);

    var addr2 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset;
    var new_globals2 := global_write_at_vaddr32(new_globals1, G_EEHCI_MEM(), addr2, eEHCI_Config_Disable);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals1, new_globals2, eehci_slot_id, G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset, eEHCI_Config_Disable);

    var addr3 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset;
    var new_globals3 := global_write_at_vaddr32(new_globals2, G_EEHCI_MEM(), addr3, 0);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals2, new_globals3, eehci_slot_id, G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset, 0);

    var addr4 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset;
    var new_globals4 := global_write_at_vaddr32(new_globals3, G_EEHCI_MEM(), addr4, eEHCI_Intr_Disable);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals3, new_globals4, eehci_slot_id, G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset, eEHCI_Intr_Disable);

    var addr5 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset;
    var new_globals5 := global_write_at_vaddr32(new_globals4, G_EEHCI_MEM(), addr5, 0);
    Lemma_WK_EEHCI_Mem_PreserveOtherEEHCISlotsIfModifyingOneSlot(new_globals4, new_globals5, eehci_slot_id, G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset, 0);

    assert new_globals == new_globals5;
}




/*********************** Lemma for <g_usbtd_map_mem> Modification  ********************/
// Lemma: When updating the PID field of a eEHCI-unreferenced USB TD, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdatePIDOfEEHCIUnrefedUSBTD(
    old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32, field_vaddr:vaddr, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid
    requires field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), field_vaddr)

    requires eehci_mem_no_ref_to_usbtd_slot(old_globals, usbtd_slot_id)
        // Requirement: No eEHCI refs the USB TD at current

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_USBTD_MAP_MEM(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    reveal p_usbtd_equal();
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_PID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_PID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_PID_BytesOffset, new_v);

    forall eehci_slot, usbtd_reg_id, usbtd_slot_id2 | eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id2 == eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id)
        ensures (usbtd_slot_id2 == USBTD_SlotID_INVALID ||
                usbtd_map_get_pid(old_globals, usbtd_slot_id2) == usbtd_map_get_pid(new_globals, usbtd_slot_id2))
    {
        assert eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id);

        var usbtd_slot_id2 := eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id);
        if(usbtd_slot_id2 != USBTD_SlotID_INVALID)
        {
            assert usbtd_slot_id2 != usbtd_slot_id;
            Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_PID_BytesOffset, new_v);
        }
    }

    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(old_globals, new_globals);
}

// Lemma: When updating the flag field of a eEHCI-unreferenced USB TD, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateFlagOfEEHCIUnrefedUSBTD(
    old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32, field_vaddr:vaddr, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid
    requires field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), field_vaddr)

    requires eehci_mem_no_ref_to_usbtd_slot(old_globals, usbtd_slot_id)
        // Requirement: No eEHCI refs the USB TD at current

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_USBTD_MAP_MEM(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    reveal p_usbtd_equal();

    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_v);

    forall eehci_slot, usbtd_reg_id, usbtd_slot_id2 | eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id2 == eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id)
        ensures (usbtd_slot_id2 == USBTD_SlotID_INVALID ||
                usbtd_map_get_flags(old_globals, usbtd_slot_id2) == usbtd_map_get_flags(new_globals, usbtd_slot_id2))
    {
        assert eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id);

        var usbtd_slot_id2 := eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id);
        if(usbtd_slot_id2 != USBTD_SlotID_INVALID)
        {
            assert usbtd_slot_id2 != usbtd_slot_id;
            Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_v);
        }
    }

    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(old_globals, new_globals);
}

// Lemma: When updating the <bus_id> field of a eEHCI-unreferenced USB TD, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateBusIDOfEEHCIUnrefedUSBTD(
    old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32, field_vaddr:vaddr, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid
    requires field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), field_vaddr)

    requires eehci_mem_no_ref_to_usbtd_slot(old_globals, usbtd_slot_id)
        // Requirement: No eEHCI refs the USB TD at current

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_USBTD_MAP_MEM(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    reveal p_usbtd_equal();

    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, new_v);

    forall eehci_slot, usbtd_reg_id, usbtd_slot_id2 | eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id2 == eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id)
        ensures (usbtd_slot_id2 == USBTD_SlotID_INVALID ||
                usbtd_map_get_busid_word(old_globals, usbtd_slot_id2) == usbtd_map_get_busid_word(new_globals, usbtd_slot_id2))
    {
        assert eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id);

        var usbtd_slot_id2 := eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id);
        if(usbtd_slot_id2 != USBTD_SlotID_INVALID)
        {
            assert usbtd_slot_id2 != usbtd_slot_id;
            Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, new_v);
        }
    }

    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(old_globals, new_globals);
}

// Lemma: When updating the <type> field of a USB TD, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateTypeOfUSBTD(
    old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32, field_vaddr:vaddr, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid
    requires field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), field_vaddr)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_USBTD_MAP_MEM(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, new_v);

    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(old_globals, new_globals);
}

// Lemma: When updating the <wimpdrv_slot_id> field of a USB TD, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateWimpDrvSlotIDOfUSBTD(
    old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32, field_vaddr:vaddr, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid
    requires field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), field_vaddr)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_USBTD_MAP_MEM(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, new_v);

    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(old_globals, new_globals);
}

// Lemma: When updating the <usbpdev_slot_id> field of a USB TD, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateUSBPDevSlotIDOfUSBTD(
    old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32, field_vaddr:vaddr, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid
    requires field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), field_vaddr)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_USBTD_MAP_MEM(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, new_v);

    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(old_globals, new_globals);
}

// Lemma: When updating the <handle> field of a USB TD, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateHandleOfUSBTD(
    old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32, field_vaddr:vaddr, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid
    requires field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), field_vaddr)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_USBTD_MAP_MEM(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, new_v);

    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(old_globals, new_globals);
}


// Lemma: When updating the <input_paramN> field of a USB TD, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateInputParamOfUSBTD(
    old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32, field_vaddr:vaddr, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid
    requires field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset ||
             field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset ||
             field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), field_vaddr)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_USBTD_MAP_MEM(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    if(field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset)
    {
        Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset, new_v);
        Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset, new_v);
        Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset, new_v);
        Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset, new_v);
    }
    else if (field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset)
    {
        Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, new_v);
        Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, new_v);
        Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, new_v);
        Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, new_v);
    }
    else
    {
        Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_v);
        Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_v);
        Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_v);
        Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, new_v);
    }
    
    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(old_globals, new_globals);
}

// Lemma: When updating the <id> field of a USB TD, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfUpdateIDOfEEHCIUnrefedUSBTD(
    old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32, field_vaddr:vaddr, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid
    requires field_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot_id * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), field_vaddr)

    requires eehci_mem_no_ref_to_usbtd_slot(old_globals, usbtd_slot_id)
        // Requirement: No eEHCI refs the USB TD at current

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_USBTD_MAP_MEM(), field_vaddr, new_v)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    reveal p_usbtd_equal();
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_ID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_ID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_ID_BytesOffset, new_v);

    forall eehci_slot, usbtd_reg_id, usbtd_slot_id2 | eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id2 == eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id)
        ensures (usbtd_slot_id2 == USBTD_SlotID_INVALID ||
                usbtd_map_get_idword(old_globals, usbtd_slot_id2) == usbtd_map_get_idword(new_globals, usbtd_slot_id2))
    {
        assert eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id);

        var usbtd_slot_id2 := eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id);
        if(usbtd_slot_id2 != USBTD_SlotID_INVALID)
        {
            assert usbtd_slot_id2 != usbtd_slot_id;
            Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(old_globals, new_globals, usbtd_slot_id, G_USBTDs_MAP_ENTRY_ID_BytesOffset, new_v);
        }
    }

    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(old_globals, new_globals);
}




/*********************** Lemma for <g_usbtd_map_mem> backup, restore and clear  ********************/
// Lemma: When restoring a USB TD from the g_temp_usbtd, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfRestoreUSBTDFromTempTD(
    old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid

    requires eehci_mem_no_ref_to_usbtd_slot(old_globals, usbtd_slot_id)
        // Requirement: No eEHCI refs the USB TD at current

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires ffi_usbtd_restore_stack_and_globals_inner(old_globals, new_globals, usbtd_slot_id)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
{
    reveal ffi_usbtd_restore_stack_and_globals_inner();
    reveal p_usbtd_equal();

    assert usbtd_map_modify_one_usbtd_only(old_globals, new_globals, usbtd_slot_id);
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    forall eehci_slot, usbtd_reg_id, usbtd_slot_id | eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id)
        ensures (usbtd_slot_id == USBTD_SlotID_INVALID ||
                usbtd_map_get_flags(old_globals, usbtd_slot_id) == usbtd_map_get_flags(new_globals, usbtd_slot_id))
    {
        var old_usbtd_slot := eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id);
        var new_usbtd_slot := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id);
        assert old_usbtd_slot  == new_usbtd_slot;
                

        if(old_usbtd_slot != USBTD_SlotID_INVALID)
        {
            assert usbtd_map_get_flags(old_globals, old_usbtd_slot) == usbtd_map_get_flags(new_globals, old_usbtd_slot);
        }
    }

    Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(old_globals, new_globals);
}

// Lemma: When restoring a USB TD from the g_temp_usbtd, the result global variable must satisfy 
// WK_EEHCI_Mem_Valid(AndSecure)GlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfRestoreUSBTDFromTempTD(
    old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid

    requires eehci_mem_no_ref_to_usbtd_slot(old_globals, usbtd_slot_id)
        // Requirement: No eEHCI refs the USB TD at current

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires ffi_usbtd_restore_stack_and_globals_inner(old_globals, new_globals, usbtd_slot_id)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(new_globals)
{
    reveal ffi_usbtd_restore_stack_and_globals_inner();
    reveal p_usbtd_equal();

    assert usbtd_map_modify_one_usbtd_only(old_globals, new_globals, usbtd_slot_id);
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    forall eehci_slot, usbtd_reg_id, usbtd_slot_id | eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id)
        ensures (usbtd_slot_id == USBTD_SlotID_INVALID ||
                usbtd_map_get_flags(old_globals, usbtd_slot_id) == usbtd_map_get_flags(new_globals, usbtd_slot_id))
    {
        var old_usbtd_slot := eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id);
        var new_usbtd_slot := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id);
        assert old_usbtd_slot  == new_usbtd_slot;
                

        if(old_usbtd_slot != USBTD_SlotID_INVALID)
        {
            assert usbtd_map_get_flags(old_globals, old_usbtd_slot) == usbtd_map_get_flags(new_globals, old_usbtd_slot);
        }
    }

    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(old_globals, new_globals);
}

// Lemma: When restoring the temp USB TD to a USB TD not checked yet, the result global variable must  
// satisfy WK_USBTD_Map_SecureGlobalVarValues
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfRestoreUSBTDFromTempTD(old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(old_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(old_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(new_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(new_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid

    requires usbtd_temp_get_flags(old_globals) == 0
        // Requirement: The flag of the temp USB TD is 0
    requires TestBit(usbtd_map_get_flags(old_globals, usbtd_slot_id), USBTD_SLOT_FLAG_SlotSecure_Bit) == false
        // Requirement: Must not restore to a verified/secure USB TD

    requires WK_USBTD_Map_SecureGlobalVarValues(old_globals)
    requires ffi_usbtd_restore_stack_and_globals_inner(old_globals, new_globals, usbtd_slot_id)
    
    ensures WK_USBTD_Map_SecureGlobalVarValues(new_globals)
{
    reveal ffi_usbtd_restore_stack_and_globals_inner();

    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();


    assert usbtd_map_modify_one_usbtd_only(old_globals, new_globals, usbtd_slot_id);
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfRestoreUSBTDFromTempTD_qTD32(old_globals, new_globals, usbtd_slot_id);
    Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfRestoreUSBTDFromTempTD_qh32(old_globals, new_globals, usbtd_slot_id);

    // [TODO] Not support iTD and siTD yet
    forall i:uint32 | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(new_globals, i) == USBTDs_TYPE_iTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_iTD32(new_globals, i)
    {
        assert usbtd_map_get_flags(new_globals, usbtd_slot_id) == 0;

        // Prove i != usbtd_slot_id
        Lemma_TestBit_ReturnFalseIfANumberIs0();
        if(i == usbtd_slot_id)
        {
            assert false;
        }
        assert i != usbtd_slot_id;

        var new_usbtd_flags := usbtd_map_get_flags(new_globals, i);
        var new_usbtd_types := usbtd_map_get_type(new_globals, i);
        var old_usbtd_flags := usbtd_map_get_flags(old_globals, i);
        var old_usbtd_types := usbtd_map_get_type(old_globals, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;
    }

    forall i:uint32 | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(new_globals, i) == USBTDs_TYPE_siTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_siTD32(new_globals, i)
    {
        assert usbtd_map_get_flags(new_globals, usbtd_slot_id) == 0;

        // Prove i != usbtd_slot_id
        Lemma_TestBit_ReturnFalseIfANumberIs0();
        if(i == usbtd_slot_id)
        {
            assert false;
        }
        assert i != usbtd_slot_id;

        var new_usbtd_flags := usbtd_map_get_flags(new_globals, i);
        var new_usbtd_types := usbtd_map_get_type(new_globals, i);
        var old_usbtd_flags := usbtd_map_get_flags(old_globals, i);
        var old_usbtd_types := usbtd_map_get_type(old_globals, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;
    }
}

// Lemma: When clearing the content of a USB TD, the result global variable must satisfy 
// WK_EEHCI_Mem_ValidGlobalVarValues
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfClearUSBTD(
    old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid

    requires eehci_mem_no_ref_to_usbtd_slot(old_globals, usbtd_slot_id)
        // Requirement: No eEHCI refs the USB TD at current

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires usbtd_map_modify_one_usbtd_only(old_globals, new_globals, usbtd_slot_id)
    
    ensures WK_EEHCI_Mem_ValidGlobalVarValues(new_globals)
{
    reveal p_usbtd_equal();

    assert usbtd_map_modify_one_usbtd_only(old_globals, new_globals, usbtd_slot_id);
    assert global_read_fullval(old_globals, G_EEHCI_MEM()) == global_read_fullval(new_globals, G_EEHCI_MEM());

    forall eehci_slot, usbtd_reg_id, usbtd_slot_id | eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id)
        ensures (usbtd_slot_id == USBTD_SlotID_INVALID ||
                usbtd_map_get_flags(old_globals, usbtd_slot_id) == usbtd_map_get_flags(new_globals, usbtd_slot_id))
    {
        var old_usbtd_slot := eehci_mem_get_usbtd_reg(old_globals, eehci_slot, usbtd_reg_id);
        var new_usbtd_slot := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, usbtd_reg_id);
        assert old_usbtd_slot  == new_usbtd_slot;
                

        if(old_usbtd_slot != USBTD_SlotID_INVALID)
        {
            assert usbtd_map_get_flags(old_globals, old_usbtd_slot) == usbtd_map_get_flags(new_globals, old_usbtd_slot);
        }
    }

    Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(old_globals, new_globals);
}




/*********************** Other Public Lemmas  ********************/
// Lemma: If two global variables have the same G_EEHCI_MEM(), then eehci_mem_all_existing_eehci_id_vals are same
lemma Lemma_EEHCI_Mem_Same_eehci_mem_all_existing_eehci_id_vals_IfGEEHCIMEMIsUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2, G_EEHCI_MEM()) 

    ensures eehci_mem_all_existing_eehci_id_vals(globals1) == eehci_mem_all_existing_eehci_id_vals(globals2)
{
    forall e | e in eehci_mem_all_existing_eehci_id_vals(globals1) 
        ensures e in eehci_mem_all_existing_eehci_id_vals(globals2)
    {
        var slot :| 0 <= slot < eEHCI_INSTANCE_NUM && 
                        eehci_mem_get_eehci_id(globals1, slot) == e &&
                        e != eEHCI_ID_INVALID;

        assert eehci_mem_get_eehci_id(globals2, slot) == e;
    }

    forall e | e in eehci_mem_all_existing_eehci_id_vals(globals2) 
        ensures e in eehci_mem_all_existing_eehci_id_vals(globals1)
    {
        var slot :| 0 <= slot < eEHCI_INSTANCE_NUM && 
                        eehci_mem_get_eehci_id(globals2, slot) == e &&
                        e != eEHCI_ID_INVALID;

        assert eehci_mem_get_eehci_id(globals1, slot) == e;
    }
}

// Lemma: If <g_eehcis_info>, <g_eehci_mem> and some USBTD fields are unchanged, and
// WK_EEHCI_Mem_ValidGlobalVarValues(globals1), Then WK_EEHCI_Mem_ValidGlobalVarValues(globals2)
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(globals1)

    requires global_read_fullval(globals1, G_EEHCIs_Info()) == global_read_fullval(globals2, G_EEHCIs_Info())
    requires global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2, G_EEHCI_MEM())
        // Requirement: <g_eehcis_info> and <g_eehci_mem> are unchanged
    requires global_read_fullval(globals1, G_EEHCI_MEM_PBASE()) == global_read_fullval(globals2, G_EEHCI_MEM_PBASE())
        // Requirement: <g_eehci_mem_pbase> is never modified
    requires forall eehci_slot, usbtd_reg_id, usbtd_slot_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id)
        ==> (usbtd_slot_id == USBTD_SlotID_INVALID ||
                usbtd_map_get_flags(globals1, usbtd_slot_id) == usbtd_map_get_flags(globals2, usbtd_slot_id))
    requires forall eehci_slot, usbtd_reg_id, usbtd_slot_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id)
        ==> (usbtd_slot_id == USBTD_SlotID_INVALID ||
                usbtd_map_get_pid(globals1, usbtd_slot_id) == usbtd_map_get_pid(globals2, usbtd_slot_id))
    requires forall eehci_slot, usbtd_reg_id, usbtd_slot_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id)
        ==> (usbtd_slot_id == USBTD_SlotID_INVALID ||
                usbtd_map_get_busid_word(globals1, usbtd_slot_id) == usbtd_map_get_busid_word(globals2, usbtd_slot_id))
        // Requirement: The USBTD slots refed in USBTD regs are unchanged

    ensures WK_EEHCI_Mem_ValidGlobalVarValues(globals2)
{
    Lemma_P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI_HoldIfEEHCIIDsAndUSBTDRegsAndRefedUSBTDSlotsAreUnchanged(globals1, globals2);
}

// Lemma: If <g_eehcis_info>, <g_eehci_mem> and some USBTD fields are unchanged, and
// WK_EEHCI_Mem_Valid(AndSecure)GlobalVarValues(globals1), Then WK_EEHCI_Mem_Valid(AndSecure)GlobalVarValues(globals2)
lemma Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(globals1)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(globals1)

    requires global_read_fullval(globals1, G_EEHCIs_Info()) == global_read_fullval(globals2, G_EEHCIs_Info())
    requires global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2, G_EEHCI_MEM())
        // Requirement: <g_eehcis_info>, <g_eehci_mem> are unchanged
    requires global_read_fullval(globals1, G_EEHCI_MEM_PBASE()) == global_read_fullval(globals2, G_EEHCI_MEM_PBASE())
        // Requirement: <g_eehci_mem_pbase> is never modified
    requires forall eehci_slot, usbtd_reg_id, usbtd_slot_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id)
        ==> (usbtd_slot_id == USBTD_SlotID_INVALID ||
                usbtd_map_get_idword(globals1, usbtd_slot_id) == usbtd_map_get_idword(globals2, usbtd_slot_id))
    requires forall eehci_slot, usbtd_reg_id, usbtd_slot_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id)
        ==> (usbtd_slot_id == USBTD_SlotID_INVALID ||
                usbtd_map_get_flags(globals1, usbtd_slot_id) == usbtd_map_get_flags(globals2, usbtd_slot_id))
    requires forall eehci_slot, usbtd_reg_id, usbtd_slot_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id)
        ==> (usbtd_slot_id == USBTD_SlotID_INVALID ||
                usbtd_map_get_pid(globals1, usbtd_slot_id) == usbtd_map_get_pid(globals2, usbtd_slot_id))
    requires forall eehci_slot, usbtd_reg_id, usbtd_slot_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id)
        ==> (usbtd_slot_id == USBTD_SlotID_INVALID ||
                usbtd_map_get_busid_word(globals1, usbtd_slot_id) == usbtd_map_get_busid_word(globals2, usbtd_slot_id))
        // Requirement: The USBTD slots refed in USBTD regs are unchanged

    ensures WK_EEHCI_Mem_ValidGlobalVarValues(globals2)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(globals2)
{
    Lemma_P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsHaveExpectedFlags_HoldIfUSBTDRegsAndRefedUSBTDSlotsAreUnchanged(globals1, globals2);
    Lemma_P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID_HoldIfGEEHCIInfoAndUSBTDRegsAndRefedUSBTDSlotsAreUnchanged(globals1, globals2);
    Lemma_P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI_HoldIfEEHCIIDsAndUSBTDRegsAndRefedUSBTDSlotsAreUnchanged(globals1, globals2);

    assert eehci_mem_pend(globals2) == eehci_mem_pend(globals1);
}

// Lemma: If <g_eehcis_info>, <g_eehci_mem> and all USBTD fields are unchanged, and
// WK_EEHCI_Mem_ValidGlobalVarValues(globals1), Then WK_EEHCI_Mem_ValidGlobalVarValues(globals2)
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(globals1)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(globals1)

    requires global_read_fullval(globals1, G_EEHCIs_Info()) == global_read_fullval(globals2, G_EEHCIs_Info())
    requires global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2, G_EEHCI_MEM())
    requires global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM())
        // Requirement: <g_eehcis_info>, <g_eehci_mem> and <g_usbtd_map_mem> are unchanged
    requires global_read_fullval(globals1, G_EEHCI_MEM_PBASE()) == global_read_fullval(globals2, G_EEHCI_MEM_PBASE())
        // Requirement: <g_eehci_mem_pbase> is never modified

    ensures WK_EEHCI_Mem_ValidGlobalVarValues(globals2)
    ensures WK_EEHCI_Mem_SecureGlobalVarValues(globals2)
{
    Lemma_WK_EEHCI_Mem_ValidAndSecureGlobalVarValues_HoldIfGEEHCIMemAndInfosAndUSBTDsAreUnchanged_USBTDInDetail(globals1, globals2);
}




/*********************** Private Lemmas ********************/
// Lemma: If USB TD regs in all eEHCIs and refed USB TD slots are unchanged, then the new global variable satisfies 
// P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags
lemma Lemma_P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsHaveExpectedFlags_HoldIfUSBTDRegsAndRefedUSBTDSlotsAreUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    
    requires (forall i :: eehci_valid_slot_id(i) ==> P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags(globals1, i))

    requires forall eehci_slot, usbtd_reg_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ==> eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(globals2, eehci_slot, usbtd_reg_id)
        // Requirement: The USBTD regs in each eEHCI is unchanged
    requires forall eehci_slot, usbtd_reg_id, usbtd_slot_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id)
        ==> (usbtd_slot_id == USBTD_SlotID_INVALID || 
                usbtd_map_get_flags(globals1, usbtd_slot_id) == usbtd_map_get_flags(globals2, usbtd_slot_id))
        // Requirement: The USBTD slots refed in USBTD regs are unchanged
        
    ensures (forall i :: eehci_valid_slot_id(i) ==> P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags(globals2, i))
{
    // Dafny can automatically prove this lemma
}

// Lemma: If G_EEHCIs_Info(), USB TD regs in all eEHCIs, and refed USB TD slots are unchanged, then the new global 
// variable satisfies P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID
lemma Lemma_P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID_HoldIfGEEHCIInfoAndUSBTDRegsAndRefedUSBTDSlotsAreUnchanged(
    globals1:globalsmap, globals2:globalsmap
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    
    requires (forall i :: eehci_valid_slot_id(i) ==> P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(globals1, i))

    requires global_read_fullval(globals1, G_EEHCIs_Info()) == global_read_fullval(globals2, G_EEHCIs_Info())
        // Requirement: G_EEHCIs_INFO is unchanged
    requires forall eehci_slot, usbtd_reg_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ==> eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(globals2, eehci_slot, usbtd_reg_id)
        // Requirement: The USBTD regs in each eEHCI is unchanged
    requires forall eehci_slot, usbtd_reg_id, usbtd_slot_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id)
        ==> (usbtd_slot_id == USBTD_SlotID_INVALID || 
                usbtd_map_get_pid(globals1, usbtd_slot_id) == usbtd_map_get_pid(globals2, usbtd_slot_id))
        // Requirement: The USBTD slots refed in USBTD regs are unchanged
        
    ensures (forall i :: eehci_valid_slot_id(i) ==> P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(globals2, i))
{
    // Dafny can automatically prove this lemma
}

// Lemma: If eEHCIs' IDs, USB TD regs in all eEHCIs, and refed USB TD slots are unchanged, then the new global variable satisfies 
// P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI
lemma Lemma_P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI_HoldIfEEHCIIDsAndUSBTDRegsAndRefedUSBTDSlotsAreUnchanged(
    globals1:globalsmap, globals2:globalsmap
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    
    requires (forall i :: eehci_valid_slot_id(i) ==> P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(globals1, i))

    requires forall eehci_slot :: eehci_valid_slot_id(eehci_slot)
        ==> eehci_mem_get_eehci_id(globals1, eehci_slot) == eehci_mem_get_eehci_id(globals2, eehci_slot)
        // Requirement: eEHCIs' IDs are unchanged
    requires forall eehci_slot, usbtd_reg_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ==> eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(globals2, eehci_slot, usbtd_reg_id)
        // Requirement: The USBTD regs in each eEHCI is unchanged
    requires forall eehci_slot, usbtd_reg_id, usbtd_slot_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id)
        ==> usbtd_slot_id == USBTD_SlotID_INVALID || 
                (usbtd_map_get_busid_word(globals1, usbtd_slot_id) == usbtd_map_get_busid_word(globals2, usbtd_slot_id))
        // Requirement: The USBTD slots refed in USBTD regs are unchanged
        
    ensures (forall i :: eehci_valid_slot_id(i) ==> P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(globals2, i))
{
    forall eehci_slot, usbtd_reg_id, usbtd_slot_id | eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id)
        ensures usbtd_slot_id == USBTD_SlotID_INVALID || 
                (usbtd_slot_valid_busid(globals2, usbtd_slot_id) &&
                    usbtd_map_get_busid(globals1, usbtd_slot_id) == usbtd_map_get_busid(globals2, usbtd_slot_id))
    {
        if(usbtd_slot_id != USBTD_SlotID_INVALID)
        {
            assert usbtd_map_get_busid_word(globals1, usbtd_slot_id) == usbtd_map_get_busid_word(globals2, usbtd_slot_id);
        }
    }

    Lemma_P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI_HoldIfEEHCIIDsAndUSBTDRegsAndRefedUSBTDSlotsAreUnchanged_Inner(globals1, globals2);
}

lemma Lemma_P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI_HoldIfEEHCIIDsAndUSBTDRegsAndRefedUSBTDSlotsAreUnchanged_Inner(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    
    requires (forall i :: eehci_valid_slot_id(i) ==> P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(globals1, i))

    requires forall eehci_slot :: eehci_valid_slot_id(eehci_slot)
        ==> eehci_mem_get_eehci_id(globals1, eehci_slot) == eehci_mem_get_eehci_id(globals2, eehci_slot)
        // Requirement: eEHCI's ID are unchanged
    requires forall eehci_slot, usbtd_reg_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ==> eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id) == eehci_mem_get_usbtd_reg(globals2, eehci_slot, usbtd_reg_id)
        // Requirement: The USBTD regs in each eEHCI is unchanged
    requires forall eehci_slot, usbtd_reg_id, usbtd_slot_id :: eehci_valid_slot_id(eehci_slot) && 
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS &&
            usbtd_slot_id == eehci_mem_get_usbtd_reg(globals1, eehci_slot, usbtd_reg_id)
        ==> (usbtd_slot_id == USBTD_SlotID_INVALID || 
                (usbtd_slot_valid_busid(globals2, usbtd_slot_id) &&
                 usbtd_map_get_busid(globals1, usbtd_slot_id) == usbtd_map_get_busid(globals2, usbtd_slot_id)))
        // Requirement: The USBTD slots refed in USBTD regs are unchanged
        
    ensures (forall i :: eehci_valid_slot_id(i) ==> P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(globals2, i))
{
    // Dafny can automatically prove this lemma
}

// Lemma: Writing one eEHCI's USBTD_reg does not change properties of other eEHCIs' memory
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteUSBTDReg_DoNotImpactOtherEEHCIMem(
    old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, usbtd_reg_id:uint32, field_vaddr:vaddr, new_usbtd_slot_id:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
    requires 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        // Requirement: <eehci_slot> and <usbtd_reg_id> are valid
    requires field_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), field_vaddr)

    requires WK_EEHCI_Mem_ValidGlobalVarValues(old_globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(old_globals)
    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), field_vaddr, new_usbtd_slot_id)

    ensures forall i :: eehci_valid_slot_id(i) && i != eehci_slot
        ==> (P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveValidIDWords(new_globals, i) &&
             P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags(new_globals, i) &&
             P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(new_globals, i) &&
             P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(new_globals, i))
{
    forall i | eehci_valid_slot_id(i) && i != eehci_slot
        ensures P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveValidIDWords(new_globals, i)
        ensures P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags(new_globals, i)
        ensures P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(new_globals, i)
        ensures P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(new_globals, i)
    {
        assert forall usbtd_reg_id :: 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
            ==> eehci_mem_get_usbtd_reg(old_globals, i, usbtd_reg_id) == eehci_mem_get_usbtd_reg(new_globals, i, usbtd_reg_id);
    }
}

// Lemma: Writing one eEHCI's USBTD_reg makes the EEHCI still fulfils P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveValidIDWords
lemma Lemma_WK_EEHCI_Mem_SecureGlobalVarValues_HoldIfWriteUSBTDReg_ModifyingEEHCI_ProveRefedTDsHaveValidIDWords(
    old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, usbtd_reg_id:uint32, field_vaddr:vaddr, new_usbtd_slot_id:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
    requires 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        // Requirement: <eehci_slot> and <usbtd_reg_id> are valid
    requires field_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), field_vaddr)

    requires new_usbtd_slot_id == USBTD_SlotID_INVALID || usbtd_map_valid_slot_id(new_usbtd_slot_id)
    requires usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> (
            var usbtd_idword := usbtd_map_get_idword(old_globals, new_usbtd_slot_id);
            usbtd_idword != USBTD_ID_INVALID
        )
        // Requirement: The ID of newly refed USB TD is good

    requires P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveValidIDWords(old_globals, eehci_slot)
    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), field_vaddr, new_usbtd_slot_id)
    
    ensures P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveValidIDWords(new_globals, eehci_slot)
{
    forall cur_usbtd_reg_id | 0 <= cur_usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ensures (
                    var usbtd_slot_id := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id);
                    usbtd_slot_id == USBTD_SlotID_INVALID || 
                        (usbtd_map_valid_slot_id(usbtd_slot_id) &&
                            // Properties needed by the following property
                            (
                                var usbtd_idword := usbtd_map_get_idword(new_globals, usbtd_slot_id);
                                usbtd_idword != USBTD_ID_INVALID
                            )
                        )
                )
    {
        var usbtd_slot_id1 := eehci_mem_get_usbtd_reg(old_globals, eehci_slot, cur_usbtd_reg_id);
        var usbtd_slot_id2 := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id);

        if(cur_usbtd_reg_id != usbtd_reg_id)
        {
            assert usbtd_slot_id2 == usbtd_slot_id1;
        }
        else
        {
            assert eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id) == new_usbtd_slot_id;
        }
    }
}

// Lemma: Writing one eEHCI's USBTD_reg makes the EEHCI still fulfils P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteUSBTDReg_ModifyingEEHCI_ProveRefedTDsHaveExpectedFlags(
    old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, usbtd_reg_id:uint32, field_vaddr:vaddr, new_usbtd_slot_id:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
    requires 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        // Requirement: <eehci_slot> and <usbtd_reg_id> are valid
    requires field_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), field_vaddr)

    requires new_usbtd_slot_id == USBTD_SlotID_INVALID || usbtd_map_valid_slot_id(new_usbtd_slot_id)
    requires usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> (
            var usbtd_flags := usbtd_map_get_flags(old_globals, new_usbtd_slot_id);
            usbtd_flags == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
        )
        // Requirement: The flags of newly refed USB TD is good

    requires P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags(old_globals, eehci_slot)
    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), field_vaddr, new_usbtd_slot_id)
    
    ensures P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags(new_globals, eehci_slot)
{
    forall cur_usbtd_reg_id | 0 <= cur_usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ensures (
                    var usbtd_slot_id := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id);
                    usbtd_slot_id == USBTD_SlotID_INVALID || 
                        (usbtd_map_valid_slot_id(usbtd_slot_id) &&
                            // Properties needed by the following property
                            (
                                var usbtd_slot_id := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id);
                                var usbtd_flags := usbtd_map_get_flags(new_globals, usbtd_slot_id);

                                // In given eEHCI, all refed TDs must have <USBTD_SLOT_FLAG_SubmitDone_Bit> and <USBTD_SLOT_FLAG_SlotSecure_Bit> set
                                usbtd_flags == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
                            )
                        )
                )
    {
        var usbtd_slot_id1 := eehci_mem_get_usbtd_reg(old_globals, eehci_slot, cur_usbtd_reg_id);
        var usbtd_slot_id2 := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id);

        if(cur_usbtd_reg_id != usbtd_reg_id)
        {
            assert usbtd_slot_id2 == usbtd_slot_id1;
        }
        else
        {
            assert eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id) == new_usbtd_slot_id;
        }
    }
}

// Lemma: Writing one eEHCI's USBTD_reg makes the EEHCI still fulfils P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteUSBTDReg_ModifyingEEHCI_ProveEEHCIAndRefedTDsSamePID(
    old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, usbtd_reg_id:uint32, field_vaddr:vaddr, new_usbtd_slot_id:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
    requires 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        // Requirement: <eehci_slot> and <usbtd_reg_id> are valid
    requires field_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), field_vaddr)

    requires new_usbtd_slot_id == USBTD_SlotID_INVALID || usbtd_map_valid_slot_id(new_usbtd_slot_id)
    requires usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> (
            var eehci_pid := eehci_info_get_pid(old_globals, eehci_slot);
            var usbtd_pid := usbtd_map_get_pid(old_globals, new_usbtd_slot_id);
            eehci_pid == usbtd_pid
        )
        // Requirement: The PID of newly refed USB TD is good

    requires P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(old_globals, eehci_slot)
    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), field_vaddr, new_usbtd_slot_id)
    
    ensures P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(new_globals, eehci_slot)
{
    var eehci_pid := eehci_info_get_pid(new_globals, eehci_slot);

    forall cur_usbtd_reg_id | 0 <= cur_usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ensures (
                    var usbtd_slot_id := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id);
                    usbtd_slot_id == USBTD_SlotID_INVALID || 
                        (usbtd_map_valid_slot_id(usbtd_slot_id) &&
                            // Properties needed by the following property
                            (
                                var usbtd_slot_id := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id);
                                var usbtd_pid := usbtd_map_get_pid(new_globals, usbtd_slot_id);

                                // In given eEHCI, all refed TDs must be in the same partition with the eEHCI
                                eehci_pid == usbtd_pid
                            )
                        )
                )
    {
        var usbtd_slot_id1 := eehci_mem_get_usbtd_reg(old_globals, eehci_slot, cur_usbtd_reg_id);
        var usbtd_slot_id2 := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id);

        if(cur_usbtd_reg_id != usbtd_reg_id)
        {
            assert usbtd_slot_id2 == usbtd_slot_id1;
        }
        else
        {
            assert eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id) == new_usbtd_slot_id;
        }
    }
}

// Lemma: Writing one eEHCI's USBTD_reg makes the EEHCI still fulfils P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI
lemma Lemma_WK_EEHCI_Mem_ValidGlobalVarValues_HoldIfWriteUSBTDReg_ModifyingEEHCI_ProveRefedTDsTargetUSBBusOfEEHCI(
    old_globals:globalsmap, new_globals:globalsmap, eehci_slot:uint32, usbtd_reg_id:uint32, field_vaddr:vaddr, new_usbtd_slot_id:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires eehci_valid_slot_id(eehci_slot)
    requires 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        // Requirement: <eehci_slot> and <usbtd_reg_id> are valid
    requires field_vaddr == AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES
    requires is_gvar_valid_vaddr(G_EEHCI_MEM(), field_vaddr)

    requires new_usbtd_slot_id == USBTD_SlotID_INVALID || usbtd_map_valid_slot_id(new_usbtd_slot_id)
    requires usbtd_map_valid_slot_id(new_usbtd_slot_id) ==> (
            usbtd_slot_valid_busid(old_globals, new_usbtd_slot_id)
        ) &&
        (
            var eehci_busid:uint16 := usb_parse_eehci_id(eehci_mem_get_eehci_id(old_globals, eehci_slot)).bus_id;
            var usbtd_busid:uint16 := usbtd_map_get_busid(old_globals, new_usbtd_slot_id);
            eehci_busid == usbtd_busid
        )
        // Requirement: The bus id of newly refed USB TD is good

    requires P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(old_globals, eehci_slot)
    requires new_globals == global_write_word(old_globals, G_EEHCI_MEM(), field_vaddr, new_usbtd_slot_id)
    
    ensures P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(new_globals, eehci_slot)
{
    var eehci_busid:uint16 := usb_parse_eehci_id(eehci_mem_get_eehci_id(new_globals, eehci_slot)).bus_id;

    forall cur_usbtd_reg_id | 0 <= cur_usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ensures (
                var usbtd_slot_id := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id);
                usbtd_slot_id == USBTD_SlotID_INVALID || 
                    (usbtd_map_valid_slot_id(usbtd_slot_id) &&
                     usbtd_slot_valid_busid(new_globals, usbtd_slot_id) &&
                        // Properties needed by the following property
                        (
                            var usbtd_slot_id := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id);
                            var usbtd_busid:uint16 := usbtd_map_get_busid(new_globals, usbtd_slot_id);

                            // In given eEHCI, all refed TDs must target the USB bus supported by the eEHCI
                            eehci_busid == usbtd_busid
                        )
                    )
            )
    {
        var usbtd_slot_id1 := eehci_mem_get_usbtd_reg(old_globals, eehci_slot, cur_usbtd_reg_id);
        var usbtd_slot_id2 := eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id);

        if(cur_usbtd_reg_id != usbtd_reg_id)
        {
            assert usbtd_slot_id2 == usbtd_slot_id1;
        }
        else
        {
            assert eehci_mem_get_usbtd_reg(new_globals, eehci_slot, cur_usbtd_reg_id) == new_usbtd_slot_id;
        }
    }
}

// Lemma: if G_EEHCI_MEM is unchanged, then global variable always satisfy eehci_mem_no_ref_to_usbtd_slot
lemma Lemma_eehci_mem_no_ref_to_usbtd_slot_Equivilant(globals1:globalsmap, globals2:globalsmap, usbtd_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires usbtd_map_valid_slot_id(usbtd_slot_id)

    requires global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2, G_EEHCI_MEM())
    requires eehci_mem_no_ref_to_usbtd_slot(globals1, usbtd_slot_id)
    
    ensures eehci_mem_no_ref_to_usbtd_slot(globals2, usbtd_slot_id)
{
    forall eehci_slot_id, usbtd_reg_id | eehci_valid_slot_id(eehci_slot_id) &&
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ensures (
                var ref_usbtd_slot_id := eehci_mem_get_usbtd_reg(globals2, eehci_slot_id, usbtd_reg_id);

                ref_usbtd_slot_id != usbtd_slot_id
            )
    {
        assert eehci_mem_get_usbtd_reg(globals1, eehci_slot_id, usbtd_reg_id) == eehci_mem_get_usbtd_reg(globals2, eehci_slot_id, usbtd_reg_id);
    }
}

// Lemma: if Non-Scratchpad GlobalVars is unchanged, then global variable always satisfy eehci_mem_no_ref_to_usbtd_slot
lemma Lemma_eehci_mem_no_ref_to_usbtd_slot_HoldIfOnlyScratchpadGlobalVarsModified(globals1:globalsmap, globals2:globalsmap, usbtd_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires usbtd_map_valid_slot_id(usbtd_slot_id)

    requires global_non_scratchpad_vars_are_unchanged(globals1, globals2)
    requires eehci_mem_no_ref_to_usbtd_slot(globals1, usbtd_slot_id)
    
    ensures eehci_mem_no_ref_to_usbtd_slot(globals2, usbtd_slot_id)
{
    reveal global_non_scratchpad_vars_are_unchanged();

    assert global_read_fullval(globals1, G_EEHCI_MEM()) == global_read_fullval(globals2, G_EEHCI_MEM());
    Lemma_eehci_mem_no_ref_to_usbtd_slot_Equivilant(globals1, globals2, usbtd_slot_id);
}

// Lemma: When restoring the temp USB TD to a USB TD not checked yet, the result global variable must  
// satisfy WK_USBTD_Map_SecureGlobalVarValues (qTD32 part)
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfRestoreUSBTDFromTempTD_qTD32(old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(old_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(old_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(new_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(new_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid

    requires usbtd_temp_get_flags(old_globals) == 0
        // Requirement: The flag of the temp USB TD is 0
    requires TestBit(usbtd_map_get_flags(old_globals, usbtd_slot_id), USBTD_SLOT_FLAG_SlotSecure_Bit) == false
        // Requirement: Must not restore to a verified/secure USB TD

    requires WK_USBTD_Map_SecureGlobalVarValues(old_globals)
    requires ffi_usbtd_restore_stack_and_globals_inner(old_globals, new_globals, usbtd_slot_id)
    
    ensures (forall i :: usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(new_globals, i) == USBTDs_TYPE_QTD32)
        ==> WK_USBTD_Map_SecureGlobalVarValues_qTD32(new_globals, i))
{
    reveal ffi_usbtd_restore_stack_and_globals_inner();

    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();


    assert usbtd_map_modify_one_usbtd_only(old_globals, new_globals, usbtd_slot_id);
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    forall i:uint32 | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(new_globals, i) == USBTDs_TYPE_QTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qTD32(new_globals, i)
    {
        assert usbtd_map_get_flags(new_globals, usbtd_slot_id) == 0;

        // Prove i != usbtd_slot_id
        Lemma_TestBit_ReturnFalseIfANumberIs0();
        if(i == usbtd_slot_id)
        {
            assert false;
        }
        assert i != usbtd_slot_id;

        var new_usbtd_flags := usbtd_map_get_flags(new_globals, i);
        var new_usbtd_types := usbtd_map_get_type(new_globals, i);
        var old_usbtd_flags := usbtd_map_get_flags(old_globals, i);
        var old_usbtd_types := usbtd_map_get_type(old_globals, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;

        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(old_globals, i);
        Lemma_WK_USBTD_Map_SecureGlobalVarValues_qTD32_Properties(old_globals, i);
        var drv_slot := usbtd_map_get_wimpdrv_slotid(new_globals, i);
        var drv_id := wimpdrv_get_id_word(new_globals, drv_slot);
        var drv_pid := wimpdrv_get_pid(new_globals, drv_slot);

        // Prove p__usbtd_verify_qtd32_step2_OnSuccessCheck(new_globals, drv_pid.v, i);
        var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + UINT32_BYTES);
        var next_qtd_slot1:uint32 := RightShift(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot1:uint32 := RightShift(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var alt_next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

        var next_qtd_slot2:uint32 := RightShift(global_read_uint32(new_globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot2:uint32 := RightShift(global_read_uint32(new_globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(new_globals, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var alt_next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(new_globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

        assert next_qtd_slot1 == next_qtd_slot2;
        assert alt_next_qtd_slot1 == alt_next_qtd_slot2;
        assert next_qtd_p_Tflag1 == next_qtd_p_Tflag2;
        assert alt_next_qtd_p_Tflag1 == alt_next_qtd_p_Tflag2;

        if(next_qtd_p_Tflag1 != 1)
        {
            assert next_qtd_slot1 != usbtd_slot_id;
            assert usbtd_map_modify_one_usbtd_only(old_globals, new_globals, usbtd_slot_id);
            reveal p_usbtd_equal();

            assert usbtd_map_valid_slot_id(next_qtd_slot1);
            assert usbtd_map_get_pid(old_globals, next_qtd_slot1) == usbtd_map_get_pid(new_globals, next_qtd_slot1);
            assert TestBit(usbtd_map_get_flags(new_globals, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }

        if(alt_next_qtd_p_Tflag1 != 1)
        {
            assert alt_next_qtd_slot1 != usbtd_slot_id;
            
            assert usbtd_map_valid_slot_id(alt_next_qtd_slot1);
            assert usbtd_map_get_pid(old_globals, alt_next_qtd_slot1) == usbtd_map_get_pid(new_globals, alt_next_qtd_slot1);
            assert TestBit(usbtd_map_get_flags(new_globals, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }

        assert p__usbtd_verify_qtd32_step2_OnSuccessCheck(new_globals, drv_pid.v, i);

        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(old_globals, new_globals, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(new_globals, i);
    }
}

// Lemma: When restoring the temp USB TD to a USB TD not checked yet, the result global variable must  
// satisfy WK_USBTD_Map_SecureGlobalVarValues (QH32 part)
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfRestoreUSBTDFromTempTD_qh32(old_globals:globalsmap, new_globals:globalsmap, usbtd_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(old_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(old_globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(new_globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(new_globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
        // Requirement: <usbtd_slot_id> is valid

    requires usbtd_temp_get_flags(old_globals) == 0
        // Requirement: The flag of the temp USB TD is 0
    requires TestBit(usbtd_map_get_flags(old_globals, usbtd_slot_id), USBTD_SLOT_FLAG_SlotSecure_Bit) == false
        // Requirement: Must not restore to a verified/secure USB TD

    requires WK_USBTD_Map_SecureGlobalVarValues(old_globals)
    requires ffi_usbtd_restore_stack_and_globals_inner(old_globals, new_globals, usbtd_slot_id)
    
    ensures (forall i :: usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(new_globals, i) == USBTDs_TYPE_QH32)
        ==> WK_USBTD_Map_SecureGlobalVarValues_qh32(new_globals, i))
{
    reveal ffi_usbtd_restore_stack_and_globals_inner();

    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();

    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();


    assert usbtd_map_modify_one_usbtd_only(old_globals, new_globals, usbtd_slot_id);
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    forall i:uint32 | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(new_globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(new_globals, i) == USBTDs_TYPE_QH32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qh32(new_globals, i)
    {
        assert usbtd_map_get_flags(new_globals, usbtd_slot_id) == 0;

        // Prove i != usbtd_slot_id
        Lemma_TestBit_ReturnFalseIfANumberIs0();
        if(i == usbtd_slot_id)
        {
            assert false;
        }
        assert i != usbtd_slot_id;

        var new_usbtd_flags := usbtd_map_get_flags(new_globals, i);
        var new_usbtd_types := usbtd_map_get_type(new_globals, i);
        var old_usbtd_flags := usbtd_map_get_flags(old_globals, i);
        var old_usbtd_types := usbtd_map_get_type(old_globals, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;

        assert WK_USBTD_Map_SecureGlobalVarValues_qh32(old_globals, i);
        Lemma_WK_USBTD_Map_SecureGlobalVarValues_qh32_Properties(old_globals, i);
        var drv_slot := usbtd_map_get_wimpdrv_slotid(new_globals, i);
        var drv_id := wimpdrv_get_id_word(new_globals, drv_slot);
        var drv_pid := wimpdrv_get_pid(new_globals, drv_slot);

        // Prove p__usbtd_verify_qh32_step2_OnSuccessCheck(new_globals, drv_pid.v, i);
        var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 4 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 5 * UINT32_BYTES);
        var next_qh_slot1:paddr := RightShift(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var next_qtd_slot1:paddr := RightShift(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot1:paddr := RightShift(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qh_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
        var alt_next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(old_globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

        var next_qh_slot2:paddr := RightShift(global_read_uint32(new_globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var next_qtd_slot2:paddr := RightShift(global_read_uint32(new_globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot2:paddr := RightShift(global_read_uint32(new_globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qh_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(new_globals, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(new_globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
        var alt_next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(new_globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

        assert next_qh_slot1 == next_qh_slot2;
        assert next_qtd_slot1 == next_qtd_slot2;
        assert alt_next_qtd_slot1 == alt_next_qtd_slot2;
        assert next_qh_p_Tflag1 == next_qh_p_Tflag2;
        assert next_qtd_p_Tflag1 == next_qtd_p_Tflag2;
        assert alt_next_qtd_p_Tflag1 == alt_next_qtd_p_Tflag2;

        if(next_qh_p_Tflag1 != 1)
        {
            assert next_qh_slot1 != usbtd_slot_id;
            assert usbtd_map_modify_one_usbtd_only(old_globals, new_globals, usbtd_slot_id);
            reveal p_usbtd_equal();

            assert usbtd_map_valid_slot_id(next_qh_slot1);
            assert usbtd_map_get_pid(old_globals, next_qh_slot1) == usbtd_map_get_pid(new_globals, next_qh_slot1);
            assert TestBit(usbtd_map_get_flags(new_globals, next_qh_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }

        if(next_qtd_p_Tflag1 != 1)
        {
            assert next_qtd_slot1 != usbtd_slot_id;
            assert usbtd_map_modify_one_usbtd_only(old_globals, new_globals, usbtd_slot_id);
            reveal p_usbtd_equal();

            assert usbtd_map_valid_slot_id(next_qtd_slot1);
            assert usbtd_map_get_pid(old_globals, next_qtd_slot1) == usbtd_map_get_pid(new_globals, next_qtd_slot1);
            assert TestBit(usbtd_map_get_flags(new_globals, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }

        if(alt_next_qtd_p_Tflag1 != 1)
        {
            assert alt_next_qtd_slot1 != usbtd_slot_id;
            
            assert usbtd_map_valid_slot_id(alt_next_qtd_slot1);
            assert usbtd_map_get_pid(old_globals, alt_next_qtd_slot1) == usbtd_map_get_pid(new_globals, alt_next_qtd_slot1);
            assert TestBit(usbtd_map_get_flags(new_globals, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }

        assert p__usbtd_verify_qh32_step2_OnSuccessCheck(new_globals, drv_pid.v, i);

        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(old_globals, new_globals, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_qh32(new_globals, i);
    }
}