include "usb_tds.s.dfy"
include "../../state_utils.s.dfy"
include "eehci.s.dfy"
include "../../state_properties_OpsSaneStateSubset.s.dfy"
include "usb_tds_ops/usb_tds_checks.i.dfy"
include "usb_tds.i.dfy"
include "../../utils/model/utils_subjs_objs.i.dfy"

/*********************** Axioms and Useful Lemmas ********************/
// [HW] Axiom (related): If a USB TD is not refed by any other secure USB TDs, then those secure USB TDs preserve the
// property Is_USBTD_NotModifyUSBPDevsAddrs
// [NOTE] This axiom makes sense, because (1) other secure USB TDs keeps their original functionalities, no matter how
// the unrefed USB TD is modified
lemma {:axiom} Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfUnrefedUSBTDIsModified_MostFieldsEquality(
    globals1:globalsmap, globals2:globalsmap, td_slot:word, not_refed_td_slot:word
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)

    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(td_slot)
    requires usbtd_map_valid_slot_id(not_refed_td_slot)
    requires td_slot != not_refed_td_slot

    requires usbtds_verifiedtds_do_not_associate_usbtd(globals1, not_refed_td_slot)
        // Requirement: No USB TD refs the USB TD <not_refed_td_slot>
    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != not_refed_td_slot &&
                    TestBit(usbtd_map_get_flags(globals1, i), USBTD_SLOT_FLAG_SlotSecure_Bit)
                ==> (p_usbtd_content_equal(globals1, globals2, i) &&
                     usbtd_map_get_type(globals1, i) == usbtd_map_get_type(globals2, i) &&
                     usbtd_map_get_usbpdev_slotid(globals1, i) == usbtd_map_get_usbpdev_slotid(globals2, i))
        // Requirement: Secure USB TDs except the USB TD <not_refed_td_slot> are unchanged
    requires TestBit(usbtd_map_get_flags(globals1, td_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
        // Requirement: The USB TD <td_slot> is secure

    requires Is_USBTD_NotModifyUSBPDevsAddrs(globals1, td_slot)
    ensures Is_USBTD_NotModifyUSBPDevsAddrs(globals2, td_slot)


// Lemma: If a USB TD is not refed by any other secure USB TDs, then those secure USB TDs preserve the
// property Is_USBTD_NotModifyUSBPDevsAddrs
lemma Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfUnrefedUSBTDIsModified(
    globals1:globalsmap, globals2:globalsmap, td_slot:word, not_refed_td_slot:word
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)

    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(td_slot)
    requires usbtd_map_valid_slot_id(not_refed_td_slot)
    requires td_slot != not_refed_td_slot

    requires usbtds_verifiedtds_do_not_associate_usbtd(globals1, not_refed_td_slot)
        // Requirement: No USB TD refs the USB TD <not_refed_td_slot>
    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != not_refed_td_slot &&
                    TestBit(usbtd_map_get_flags(globals1, i), USBTD_SLOT_FLAG_SlotSecure_Bit)
                ==> p_usbtd_equal(globals1, globals2, i)
        // Requirement: Secure USB TDs are unchanged
    requires TestBit(usbtd_map_get_flags(globals1, td_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
        // Requirement: The USB TD <td_slot> is secure

    requires Is_USBTD_NotModifyUSBPDevsAddrs(globals1, td_slot)
    ensures Is_USBTD_NotModifyUSBPDevsAddrs(globals2, td_slot)
{
    reveal p_usbtd_equal();
    Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfUnrefedUSBTDIsModified_MostFieldsEquality(globals1, globals2, td_slot, not_refed_td_slot);
}




/*********************** Other Lemmas ********************/
// Lemma: The eEHCI returned by <usbtd_find_empty_slot> must not reference any USB TDs
lemma Lemma_usbtd_find_empty_slot_FoundSlotMustNotRefedInAnyEEHCI(globals:globalsmap, usbtd_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_EEHCI_Mem_ValidGlobalVarValues(globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(globals)

    requires usbtd_map_valid_slot_id(usbtd_slot_id)
    requires usbtd_map_get_pid(globals, usbtd_slot_id) == WS_PartitionID(PID_INVALID)

    ensures eehci_mem_no_ref_to_usbtd_slot(globals, usbtd_slot_id)
{
    // Dafny can automatically prove this lemma
}




/*********************** For Updating USBTD's flags ********************/
// Predicate: No verified/secure USB TD is associated with the given <usbtd_slot>
predicate {:opaque} usbtds_verifiedtds_do_not_associate_usbtd_qtd32(globals:globalsmap, td_slot:uint32, target_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)
{
    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(td_slot);

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + UINT32_BYTES);
    // According to EHCI specification, Section 3.5. The only differences posed by the I/O separation part of WK is that
    // the paddr of pointers are replaced to be USB TD slot IDs
    var next_qtd_slot:uint32 := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var alt_next_qtd_slot:uint32 := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
    var next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
    var alt_next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

    (next_qtd_p_Tflag == 1 || next_qtd_slot != target_slot) &&
    (alt_next_qtd_p_Tflag == 1 || alt_next_qtd_slot != target_slot)
}

// Predicate: No verified/secure USB TD is associated with the given <usbtd_slot>
predicate {:opaque} usbtds_verifiedtds_do_not_associate_usbtd_qh32(globals:globalsmap, td_slot:uint32, target_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)
{
    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_td_addr_ProveIsVAddrInGVar(td_slot);

    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(td_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 5 * UINT32_BYTES);
    // According to EHCI specification, Section 3.6. The only differences posed by the I/O separation part of WK is that
    // the paddr of pointers are replaced to be USB TD slot IDs
    var next_qh_slot:paddr := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var next_qtd_slot:paddr := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var alt_next_qtd_slot:paddr := RightShift(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
    var next_qh_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
    var next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
    var alt_next_qtd_p_Tflag:uint32 := BitwiseAnd(global_read_uint32(globals, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

    (next_qh_p_Tflag == 1 || next_qh_slot != target_slot) &&
    (next_qtd_p_Tflag == 1 || next_qtd_slot != target_slot) &&
    (alt_next_qtd_p_Tflag == 1 || alt_next_qtd_slot != target_slot)
}

// Predicate: No verified/secure USB TD is associated with the given <usbtd_slot>
predicate usbtds_verifiedtds_do_not_associate_usbtd(globals:globalsmap, usbtd_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(usbtd_slot)
{
    (forall i :: usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals, i) == USBTDs_TYPE_QTD32)
        ==> usbtds_verifiedtds_do_not_associate_usbtd_qtd32(globals, i, usbtd_slot)) &&

    (forall i :: usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals, i) == USBTDs_TYPE_QH32)
        ==> usbtds_verifiedtds_do_not_associate_usbtd_qh32(globals, i, usbtd_slot)) &&

    (true)
}

// Lemma: If G_USBTD_MAP_MEM, G_WimpDrvs_Info, and G_WimpUSBPDev_Info are unchanged, then 
// <WK_USBTD_Map_SecureGlobalVarValues> holds
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingFlagsOfUSBTDs(globals1:globalsmap, globals2:globalsmap, usbtd_slot:uint32, new_flags:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals2)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals2)

    requires usbtd_map_valid_slot_id(usbtd_slot)
    requires var slot_type := usbtd_map_get_type(globals1, usbtd_slot);
        (slot_type == USBTDs_TYPE_QTD32 && TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit)) 
            ==> WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals1, usbtd_slot);
    requires var slot_type := usbtd_map_get_type(globals1, usbtd_slot);
        (slot_type == USBTDs_TYPE_QH32 && TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit)) 
            ==> WK_USBTD_Map_SecureGlobalVarValues_qh32(globals1, usbtd_slot)
    requires var slot_type := usbtd_map_get_type(globals1, usbtd_slot);
        (slot_type == USBTDs_TYPE_iTD32 && TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit)) 
            ==> WK_USBTD_Map_SecureGlobalVarValues_iTD32(globals1, usbtd_slot)
    requires var slot_type := usbtd_map_get_type(globals1, usbtd_slot);
        (slot_type == USBTDs_TYPE_siTD32 && TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit)) 
            ==> WK_USBTD_Map_SecureGlobalVarValues_siTD32(globals1, usbtd_slot)
            // Requirement: If the new flags have the SlotSecure set, then the USB TD must be verified
    requires TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit) == false
            ==> usbtds_verifiedtds_do_not_associate_usbtd(globals1, usbtd_slot)
            // Requirement: If the new flags have no SlotSecure set, then the USB TD must not be referenced by any 
            // verified/secure USB TDs
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset;
        is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
        globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_flags)
    
    ensures WK_USBTD_Map_SecureGlobalVarValues(globals2)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();
    
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck(); // [TODO] Should be modified when we support iTD and siTD
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck(); // [TODO] Should be modified when we support iTD and siTD

    Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(globals1, globals2, usbtd_slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals1, globals2, usbtd_slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
    Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals1, globals2, usbtd_slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals1, globals2, usbtd_slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
    Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(globals1, globals2, usbtd_slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
    Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(globals1, globals2, usbtd_slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals1, globals2, usbtd_slot, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, new_flags);

    forall i:uint32 | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i)
    {
        var new_flags_securebit := TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit);
        if(new_flags_securebit)
        {
            if(i != usbtd_slot)
            {
                assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals1, i);
                Lemma_WK_USBTD_Map_SecureGlobalVarValues_ForOtherUSBTDs_HoldIfOneUSBTDIsModified_AndModifyingUSBTDKeepsSecureSlotFlag_qtd32(
                    globals1, globals2, usbtd_slot);
                assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i);
            }
            else
            {
                assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals1, i);
                Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfMostFieldsOfSecureUSBTDsAreUnchanged_QTD32(globals1, globals2, i);
                Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfOneUSBTDIsModified_AndModifyingUSBTDKeepsSecureSlotFlag_qtd32(
                    globals1, globals2, usbtd_slot);
                assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i);
            }
        }
        else
        {
            Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfOneUSBTDIsModified_AndModifyingUSBTDRemoveSecureSlotFlag_qtd32(
                globals1, globals2, usbtd_slot);
        }
    }

    forall i | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QH32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i)
    {
        var new_flags_securebit := TestBit(new_flags, USBTD_SLOT_FLAG_SlotSecure_Bit);
        if(new_flags_securebit)
        {
            if(i != usbtd_slot)
            {
                assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals1, i);
                Lemma_WK_USBTD_Map_SecureGlobalVarValues_ForOtherUSBTDs_HoldIfOneUSBTDIsModified_AndModifyingUSBTDKeepsSecureSlotFlag_qh32(
                    globals1, globals2, usbtd_slot);
                assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i);
            }
            else
            {
                assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals1, i);
                Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfMostFieldsOfSecureUSBTDsAreUnchanged_QH32(globals1, globals2, i);
                Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfOneUSBTDIsModified_AndModifyingUSBTDKeepsSecureSlotFlag_qh32(
                    globals1, globals2, usbtd_slot);
                assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i);
            }
        }
        else
        {
            Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfOneUSBTDIsModified_AndModifyingUSBTDRemoveSecureSlotFlag_qh32(
                globals1, globals2, usbtd_slot);
        }
    }
}

// Lemma: If G_USBTD_MAP_MEM, G_WimpDrvs_Info, and G_WimpUSBPDev_Info are unchanged, then 
// <WK_USBTD_Map_SecureGlobalVarValues> holds
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingInsecureUSBTDAndNotFlags(
    globals1:globalsmap, globals2:globalsmap, td_slot:uint32, offset:uint32, new_v:word
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals2)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals2)

    requires usbtd_map_valid_slot_id(td_slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires offset != G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset
        // Requirement: Not modifying <flags> of the USB TD
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + td_slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    requires TestBit(usbtd_map_get_flags(globals1, td_slot), USBTD_SLOT_FLAG_SlotSecure_Bit) == false
        // Requirement: Modifying an insecure USB TD
    
    ensures WK_USBTD_Map_SecureGlobalVarValues(globals2)
{
    reveal p_usbtd_equal(); 
    reveal p_usbtd_content_equal();
    
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals1, globals2, td_slot, offset, new_v);
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals1, globals2, td_slot, offset, new_v);

    forall i:uint32 | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i)
    {
        assert i != td_slot;

        var new_usbtd_flags := usbtd_map_get_flags(globals2, i);
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_flags := usbtd_map_get_flags(globals1, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);
        assert new_usbtd_flags == old_usbtd_flags;

        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals1, i);
        Lemma_WK_USBTD_Map_SecureGlobalVarValues_qTD32_Properties(globals1, i);
        var drv_slot := usbtd_map_get_wimpdrv_slotid(globals2, i);
        var drv_id := wimpdrv_get_id_word(globals2, drv_slot);
        var drv_pid := wimpdrv_get_pid(globals2, drv_slot);

        // Prove p__usbtd_verify_qtd32_step2_OnSuccessCheck(globals2, drv_pid.v, i);
        var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + UINT32_BYTES);
        var next_qtd_slot1:uint32 := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot1:uint32 := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var alt_next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

        var next_qtd_slot2:uint32 := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot2:uint32 := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var alt_next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

        assert next_qtd_slot1 == next_qtd_slot2;
        assert alt_next_qtd_slot1 == alt_next_qtd_slot2;
        assert next_qtd_p_Tflag1 == next_qtd_p_Tflag2;
        assert alt_next_qtd_p_Tflag1 == alt_next_qtd_p_Tflag2;

        if(next_qtd_p_Tflag1 != 1)
        {
            assert next_qtd_slot1 != td_slot;
            assert usbtd_map_modify_one_usbtd_only(globals1, globals2, td_slot);
            reveal p_usbtd_equal();

            assert usbtd_map_valid_slot_id(next_qtd_slot1);
            assert usbtd_map_get_pid(globals1, next_qtd_slot1) == usbtd_map_get_pid(globals2, next_qtd_slot1);
            assert TestBit(usbtd_map_get_flags(globals2, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }

        if(alt_next_qtd_p_Tflag1 != 1)
        {
            assert alt_next_qtd_slot1 != td_slot;
            
            assert usbtd_map_valid_slot_id(alt_next_qtd_slot1);
            assert usbtd_map_get_pid(globals1, alt_next_qtd_slot1) == usbtd_map_get_pid(globals2, alt_next_qtd_slot1);
            assert TestBit(usbtd_map_get_flags(globals2, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }

        assert p__usbtd_verify_qtd32_step2_OnSuccessCheck(globals2, drv_pid.v, i);

        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(globals1, globals2, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i);
    }

    forall i:uint32 | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QH32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i)
    {
        assert i != td_slot;

        var new_usbtd_flags := usbtd_map_get_flags(globals2, i);
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_flags := usbtd_map_get_flags(globals1, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);
        assert new_usbtd_flags == old_usbtd_flags;

        assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals1, i);
        Lemma_WK_USBTD_Map_SecureGlobalVarValues_qh32_Properties(globals1, i);
        var drv_slot := usbtd_map_get_wimpdrv_slotid(globals2, i);
        var drv_id := wimpdrv_get_id_word(globals2, drv_slot);
        var drv_pid := wimpdrv_get_pid(globals2, drv_slot);

        // Prove p__usbtd_verify_qh32_step2_OnSuccessCheck(new_globals, drv_pid.v, i);
        var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 4 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 5 * UINT32_BYTES);
        var next_qh_slot1:paddr := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var next_qtd_slot1:paddr := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot1:paddr := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qh_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
        var alt_next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

        var next_qh_slot2:paddr := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var next_qtd_slot2:paddr := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot2:paddr := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qh_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
        var alt_next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

        assert next_qh_slot1 == next_qh_slot2;
        assert next_qtd_slot1 == next_qtd_slot2;
        assert alt_next_qtd_slot1 == alt_next_qtd_slot2;
        assert next_qh_p_Tflag1 == next_qh_p_Tflag2;
        assert next_qtd_p_Tflag1 == next_qtd_p_Tflag2;
        assert alt_next_qtd_p_Tflag1 == alt_next_qtd_p_Tflag2;

        if(next_qh_p_Tflag1 != 1)
        {
            assert next_qh_slot1 != td_slot;
            assert usbtd_map_modify_one_usbtd_only(globals1, globals2, td_slot);
            reveal p_usbtd_equal();

            assert usbtd_map_valid_slot_id(next_qh_slot1);
            assert usbtd_map_get_pid(globals1, next_qh_slot1) == usbtd_map_get_pid(globals2, next_qh_slot1);
            assert TestBit(usbtd_map_get_flags(globals2, next_qh_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }

        if(next_qtd_p_Tflag1 != 1)
        {
            assert next_qtd_slot1 != td_slot;
            assert usbtd_map_modify_one_usbtd_only(globals1, globals2, td_slot);
            reveal p_usbtd_equal();

            assert usbtd_map_valid_slot_id(next_qtd_slot1);
            assert usbtd_map_get_pid(globals1, next_qtd_slot1) == usbtd_map_get_pid(globals2, next_qtd_slot1);
            assert TestBit(usbtd_map_get_flags(globals2, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }

        if(alt_next_qtd_p_Tflag1 != 1)
        {
            assert alt_next_qtd_slot1 != td_slot;
            
            assert usbtd_map_valid_slot_id(alt_next_qtd_slot1);
            assert usbtd_map_get_pid(globals1, alt_next_qtd_slot1) == usbtd_map_get_pid(globals2, alt_next_qtd_slot1);
            assert TestBit(usbtd_map_get_flags(globals2, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }

        assert p__usbtd_verify_qh32_step2_OnSuccessCheck(globals2, drv_pid.v, i);

        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(globals1, globals2, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i);
    }
}

// Lemma: If the modifying USB TD do not have SlotSecure bit set, then the new USB TD always satisfy 
// usbtds_verifiedtds_do_not_associate_usbtd
lemma Lemma_usbtds_verifiedtds_do_not_associate_usbtd_HoldIfModifyingUSBTDRemainsInsecure(globals1:globalsmap, globals2:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires TestBit(usbtd_map_get_flags(globals1, slot), USBTD_SLOT_FLAG_SlotSecure_Bit) == false;
    requires TestBit(usbtd_map_get_flags(globals2, slot), USBTD_SLOT_FLAG_SlotSecure_Bit) == false;

    requires usbtds_verifiedtds_do_not_associate_usbtd(globals1, slot)
    requires usbtd_map_modify_one_usbtd_only(globals1, globals2, slot)

    ensures usbtds_verifiedtds_do_not_associate_usbtd(globals2, slot)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();
    reveal usbtds_verifiedtds_do_not_associate_usbtd_qtd32();
    reveal usbtds_verifiedtds_do_not_associate_usbtd_qh32();
}





/*********************** For Updating USBTD's Other fields ********************/
predicate {:opaque} P_usbtd_set_id_PreConditionOfIDMappings(
    id_mappings:WSM_ID_Mappings, globals:globalsmap, usbtd_tds:set<TD_ID>, usbtd_fds:set<FD_ID>, usbtd_dos:set<DO_ID>
)
    requires WK_ValidGlobalVars_Decls(globals)
{
    forall i :: 0 <= i <= usbtd_id_counter_read(globals)
        ==> i in id_mappings.usbtd_to_td && id_mappings.usbtd_to_td[i] in usbtd_tds &&
            i in id_mappings.usbtd_to_fd && id_mappings.usbtd_to_fd[i] in usbtd_fds &&
            i in id_mappings.usbtd_to_do && id_mappings.usbtd_to_do[i] in usbtd_dos
}




/*********************** Private Lemmas For Updating USBTD's flags ********************/
// Lemma: If one verified/secure USB TD (qTD32) is modified in flags/handle/input_params, and the new USB TD has the 
// SecureBit set, then the USB TD must still be verified/secure without verification
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfOneUSBTDIsModified_AndModifyingUSBTDKeepsSecureSlotFlag_qtd32(
    globals1:globalsmap, globals2:globalsmap, usbtd_slot:uint32
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals2)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals2)
    
    requires usbtd_map_valid_slot_id(usbtd_slot)
    requires p_usbtd_content_equal(globals1, globals2, usbtd_slot)
    requires usbtd_map_get_pid(globals1, usbtd_slot) == usbtd_map_get_pid(globals2, usbtd_slot)
    requires usbtd_map_get_type(globals1, usbtd_slot) == usbtd_map_get_type(globals2, usbtd_slot)
    requires TestBit(usbtd_map_get_flags(globals2, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_wimpdrv_slotid(globals1, usbtd_slot) == usbtd_map_get_wimpdrv_slotid(globals2, usbtd_slot)
    requires usbtd_map_get_usbpdev_slotid(globals1, usbtd_slot) == usbtd_map_get_usbpdev_slotid(globals2, usbtd_slot)
    requires usbtd_map_get_busid(globals1, usbtd_slot) == usbtd_map_get_busid(globals2, usbtd_slot)
    requires Is_USBTD_NotModifyUSBPDevsAddrs(globals2, usbtd_slot)

    requires forall i :: usbtd_map_valid_slot_id(i) && i != usbtd_slot
                ==> p_usbtd_equal(globals1, globals2, i)
        // Requirement: USB TD content is unchanged
    
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info())
    
    requires WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals1, usbtd_slot)
    ensures WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, usbtd_slot)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();
    
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

    var new_usbtd_types := usbtd_map_get_type(globals2, usbtd_slot);
    var old_usbtd_types := usbtd_map_get_type(globals1, usbtd_slot);

    assert new_usbtd_types == old_usbtd_types;

    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals1, usbtd_slot);
    Lemma_WK_USBTD_Map_SecureGlobalVarValues_qTD32_Properties(globals1, usbtd_slot);
    var drv_pid := wimpdrv_get_pid(globals1, drv_slot);
    assert p__usbtd_verify_qtd32_step2_OnSuccessCheck(globals1, drv_pid.v, usbtd_slot);

    // Prove p__usbtd_verify_qtd32_step2_OnSuccessCheck(globals2, drv_pid.v, i)
    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(usbtd_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(usbtd_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + UINT32_BYTES);
    var next_qtd_slot1:uint32 := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var alt_next_qtd_slot1:uint32 := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
    var next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
    var alt_next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

    var next_qtd_slot2:uint32 := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var alt_next_qtd_slot2:uint32 := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
    var next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
    var alt_next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

    assert next_qtd_slot1 == next_qtd_slot2;
    assert alt_next_qtd_slot1 == alt_next_qtd_slot2;
    assert next_qtd_p_Tflag1 == next_qtd_p_Tflag2;
    assert alt_next_qtd_p_Tflag1 == alt_next_qtd_p_Tflag2;

    if(next_qtd_p_Tflag1 != 1)
    {
        assert (0 <= next_qtd_slot1 < USB_TD_ENTRY_NUM);

        if(next_qtd_slot1 != usbtd_slot)
        {
            assert p_usbtd_equal(globals1, globals2, next_qtd_slot1);
            assert usbtd_map_get_pid(globals1, next_qtd_slot1) == usbtd_map_get_pid(globals2, next_qtd_slot1);
            assert usbtd_map_get_flags(globals1, next_qtd_slot1) == usbtd_map_get_flags(globals2, next_qtd_slot1);

            assert usbtd_map_get_pid(globals2, next_qtd_slot1) == drv_pid;
            assert TestBit(usbtd_map_get_flags(globals2, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }
        else
        {
            assert usbtd_map_get_pid(globals2, next_qtd_slot1) == drv_pid;
            assert TestBit(usbtd_map_get_flags(globals2, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }
    }

    if(alt_next_qtd_p_Tflag1 != 1)
    {
        assert (0 <= alt_next_qtd_slot1 < USB_TD_ENTRY_NUM);

        if(alt_next_qtd_slot1 != usbtd_slot)
        {
            assert p_usbtd_equal(globals1, globals2, alt_next_qtd_slot1);
            assert usbtd_map_get_pid(globals1, alt_next_qtd_slot1) == usbtd_map_get_pid(globals2, alt_next_qtd_slot1);
            assert usbtd_map_get_flags(globals1, alt_next_qtd_slot1) == usbtd_map_get_flags(globals2, alt_next_qtd_slot1);

            assert usbtd_map_get_pid(globals2, alt_next_qtd_slot1) == drv_pid;
            assert TestBit(usbtd_map_get_flags(globals2, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }
        else
        {
            assert usbtd_map_get_pid(globals2, alt_next_qtd_slot1) == drv_pid;
            assert TestBit(usbtd_map_get_flags(globals2, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }
    }
}

// Lemma: If one verified/secure USB TD (qh32) is modified in flags/handle/input_params, and the new USB TD has the 
// SecureBit set, then the USB TD must still be verified/secure without verification
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfOneUSBTDIsModified_AndModifyingUSBTDKeepsSecureSlotFlag_qh32(
    globals1:globalsmap, globals2:globalsmap, usbtd_slot:uint32
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals2)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals2)
    
    requires usbtd_map_valid_slot_id(usbtd_slot)
    requires p_usbtd_content_equal(globals1, globals2, usbtd_slot)
    requires usbtd_map_get_pid(globals1, usbtd_slot) == usbtd_map_get_pid(globals2, usbtd_slot)
    requires usbtd_map_get_type(globals1, usbtd_slot) == usbtd_map_get_type(globals2, usbtd_slot)
    requires TestBit(usbtd_map_get_flags(globals2, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_wimpdrv_slotid(globals1, usbtd_slot) == usbtd_map_get_wimpdrv_slotid(globals2, usbtd_slot)
    requires usbtd_map_get_usbpdev_slotid(globals1, usbtd_slot) == usbtd_map_get_usbpdev_slotid(globals2, usbtd_slot)
    requires usbtd_map_get_busid(globals1, usbtd_slot) == usbtd_map_get_busid(globals2, usbtd_slot)
    requires Is_USBTD_NotModifyUSBPDevsAddrs(globals2, usbtd_slot)

    requires forall i :: usbtd_map_valid_slot_id(i) && i != usbtd_slot
                ==> p_usbtd_equal(globals1, globals2, i)
        // Requirement: USB TD content is unchanged
    
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info())
    
    requires WK_USBTD_Map_SecureGlobalVarValues_qh32(globals1, usbtd_slot)
    ensures WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, usbtd_slot)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    var new_usbtd_types := usbtd_map_get_type(globals2, usbtd_slot);
    var old_usbtd_types := usbtd_map_get_type(globals1, usbtd_slot);

    assert new_usbtd_types == old_usbtd_types;

    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals1, usbtd_slot);
    Lemma_WK_USBTD_Map_SecureGlobalVarValues_qh32_Properties(globals1, usbtd_slot);
    var drv_pid := wimpdrv_get_pid(globals1, drv_slot);
    assert p__usbtd_verify_qh32_step2_OnSuccessCheck(globals1, drv_pid.v, usbtd_slot);

    // Prove p__usbtd_verify_qh32_step2_OnSuccessCheck(new_globals, drv_pid.v, i);
    var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + usbtd_slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(usbtd_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(usbtd_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 4 * UINT32_BYTES);
    Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(usbtd_slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 5 * UINT32_BYTES);
    var next_qh_slot1:paddr := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var next_qtd_slot1:paddr := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var alt_next_qtd_slot1:paddr := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
    var next_qh_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
    var next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
    var alt_next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

    var next_qh_slot2:paddr := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var next_qtd_slot2:paddr := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
    var alt_next_qtd_slot2:paddr := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
    var next_qh_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
    var next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
    var alt_next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

    assert next_qh_slot1 == next_qh_slot2;
    assert next_qtd_slot1 == next_qtd_slot2;
    assert alt_next_qtd_slot1 == alt_next_qtd_slot2;
    assert next_qh_p_Tflag1 == next_qh_p_Tflag2;
    assert next_qtd_p_Tflag1 == next_qtd_p_Tflag2;
    assert alt_next_qtd_p_Tflag1 == alt_next_qtd_p_Tflag2;

    if(next_qh_p_Tflag1 != 1)
    {
        assert (0 <= next_qh_slot1 < USB_TD_ENTRY_NUM);

        if(next_qh_slot1 != usbtd_slot)
        {
            assert p_usbtd_equal(globals1, globals2, next_qh_slot1);
            assert usbtd_map_get_pid(globals1, next_qh_slot1) == usbtd_map_get_pid(globals2, next_qh_slot1);
            assert usbtd_map_get_flags(globals1, next_qh_slot1) == usbtd_map_get_flags(globals2, next_qh_slot1);

            assert usbtd_map_get_pid(globals2, next_qh_slot1) == drv_pid;
            assert TestBit(usbtd_map_get_flags(globals2, next_qh_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }
        else
        {
            assert usbtd_map_get_pid(globals2, next_qh_slot1) == drv_pid;
            assert TestBit(usbtd_map_get_flags(globals2, next_qh_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }
    }

    if(next_qtd_p_Tflag1 != 1)
    {
        assert (0 <= next_qtd_slot1 < USB_TD_ENTRY_NUM);

        if(next_qtd_slot1 != usbtd_slot)
        {
            assert p_usbtd_equal(globals1, globals2, next_qtd_slot1);
            assert usbtd_map_get_pid(globals1, next_qtd_slot1) == usbtd_map_get_pid(globals2, next_qtd_slot1);
            assert usbtd_map_get_flags(globals1, next_qtd_slot1) == usbtd_map_get_flags(globals2, next_qtd_slot1);

            assert usbtd_map_get_pid(globals2, next_qtd_slot1) == drv_pid;
            assert TestBit(usbtd_map_get_flags(globals2, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }
        else
        {
            assert usbtd_map_get_pid(globals2, next_qtd_slot1) == drv_pid;
            assert TestBit(usbtd_map_get_flags(globals2, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }
    }

    if(alt_next_qtd_p_Tflag1 != 1)
    {
        assert (0 <= alt_next_qtd_slot1 < USB_TD_ENTRY_NUM);

        if(alt_next_qtd_slot1 != usbtd_slot)
        {
            assert p_usbtd_equal(globals1, globals2, alt_next_qtd_slot1);
            assert usbtd_map_get_pid(globals1, alt_next_qtd_slot1) == usbtd_map_get_pid(globals2, alt_next_qtd_slot1);
            assert usbtd_map_get_flags(globals1, alt_next_qtd_slot1) == usbtd_map_get_flags(globals2, alt_next_qtd_slot1);

            assert usbtd_map_get_pid(globals2, alt_next_qtd_slot1) == drv_pid;
            assert TestBit(usbtd_map_get_flags(globals2, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }
        else
        {
            assert usbtd_map_get_pid(globals2, alt_next_qtd_slot1) == drv_pid;
            assert TestBit(usbtd_map_get_flags(globals2, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
        }
    }
}

// Lemma: If one verified/secure USB TD (qTD32) is modified in flags/handle/input_params, and the new USB TD has the 
// SecureBit set, then other verified/secure USB TDs must still be verified/secure without verification
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_ForOtherUSBTDs_HoldIfOneUSBTDIsModified_AndModifyingUSBTDKeepsSecureSlotFlag_qtd32(
    globals1:globalsmap, globals2:globalsmap, usbtd_slot:uint32
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals2)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals2)
    
    requires usbtd_map_valid_slot_id(usbtd_slot)
    requires p_usbtd_content_equal(globals1, globals2, usbtd_slot)
    requires usbtd_map_get_pid(globals1, usbtd_slot) == usbtd_map_get_pid(globals2, usbtd_slot)
    requires usbtd_map_get_type(globals1, usbtd_slot) == usbtd_map_get_type(globals2, usbtd_slot)
    requires TestBit(usbtd_map_get_flags(globals2, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_wimpdrv_slotid(globals1, usbtd_slot) == usbtd_map_get_wimpdrv_slotid(globals2, usbtd_slot)
    requires usbtd_map_get_usbpdev_slotid(globals1, usbtd_slot) == usbtd_map_get_usbpdev_slotid(globals2, usbtd_slot)
    requires usbtd_map_get_busid(globals1, usbtd_slot) == usbtd_map_get_busid(globals2, usbtd_slot)

    requires forall i :: usbtd_map_valid_slot_id(i) && i != usbtd_slot
                ==> p_usbtd_equal(globals1, globals2, i)
        // Requirement: USB TD content is unchanged
    
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info())
    
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)

    ensures forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != usbtd_slot &&
                TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
                (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QTD32)
            ==> WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();
    
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

    forall i:uint32 | usbtd_map_valid_slot_id(i) && i != usbtd_slot &&
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i)
    {
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);

        assert new_usbtd_types == old_usbtd_types;

        var drv_slot := usbtd_map_get_wimpdrv_slotid(globals1, i);
        Lemma_WK_USBTD_Map_SecureGlobalVarValues_qTD32_Properties(globals1, i);
        var drv_pid := wimpdrv_get_pid(globals1, drv_slot);
        assert p__usbtd_verify_qtd32_step2_OnSuccessCheck(globals1, drv_pid.v, i);

        // Prove p__usbtd_verify_qtd32_step2_OnSuccessCheck(globals2, drv_pid.v, i)
        var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + UINT32_BYTES);
        var next_qtd_slot1:uint32 := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot1:uint32 := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var alt_next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

        var next_qtd_slot2:uint32 := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot2:uint32 := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var alt_next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

        assert next_qtd_slot1 == next_qtd_slot2;
        assert alt_next_qtd_slot1 == alt_next_qtd_slot2;
        assert next_qtd_p_Tflag1 == next_qtd_p_Tflag2;
        assert alt_next_qtd_p_Tflag1 == alt_next_qtd_p_Tflag2;

        if(next_qtd_p_Tflag1 != 1)
        {
            assert (0 <= next_qtd_slot1 < USB_TD_ENTRY_NUM);

            if(next_qtd_slot1 != usbtd_slot)
            {
                assert p_usbtd_equal(globals1, globals2, next_qtd_slot1);
                assert usbtd_map_get_pid(globals1, next_qtd_slot1) == usbtd_map_get_pid(globals2, next_qtd_slot1);
                assert usbtd_map_get_flags(globals1, next_qtd_slot1) == usbtd_map_get_flags(globals2, next_qtd_slot1);

                assert usbtd_map_get_pid(globals2, next_qtd_slot1) == drv_pid;
                assert TestBit(usbtd_map_get_flags(globals2, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
            }
            else
            {
                assert usbtd_map_get_pid(globals2, next_qtd_slot1) == drv_pid;
                assert TestBit(usbtd_map_get_flags(globals2, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
            }
        }

        if(alt_next_qtd_p_Tflag1 != 1)
        {
            assert (0 <= alt_next_qtd_slot1 < USB_TD_ENTRY_NUM);

            if(alt_next_qtd_slot1 != usbtd_slot)
            {
                assert p_usbtd_equal(globals1, globals2, alt_next_qtd_slot1);
                assert usbtd_map_get_pid(globals1, alt_next_qtd_slot1) == usbtd_map_get_pid(globals2, alt_next_qtd_slot1);
                assert usbtd_map_get_flags(globals1, alt_next_qtd_slot1) == usbtd_map_get_flags(globals2, alt_next_qtd_slot1);

                assert usbtd_map_get_pid(globals2, alt_next_qtd_slot1) == drv_pid;
                assert TestBit(usbtd_map_get_flags(globals2, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
            }
            else
            {
                assert usbtd_map_get_pid(globals2, alt_next_qtd_slot1) == drv_pid;
                assert TestBit(usbtd_map_get_flags(globals2, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
            }
        }

        assert p__usbtd_verify_qtd32_step2_OnSuccessCheck(globals2, drv_pid.v, i);

        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfMostFieldsOfSecureUSBTDsAreUnchanged(globals1, globals2, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i);
    }
}

// Lemma: If one verified/secure USB TD (qh32) is modified in flags/handle/input_params, and the new USB TD has the 
// SecureBit set, then other verified/secure USB TDs must still be verified/secure without verification
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_ForOtherUSBTDs_HoldIfOneUSBTDIsModified_AndModifyingUSBTDKeepsSecureSlotFlag_qh32(
    globals1:globalsmap, globals2:globalsmap, usbtd_slot:uint32
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals2)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals2)
    
    requires usbtd_map_valid_slot_id(usbtd_slot)
    requires p_usbtd_content_equal(globals1, globals2, usbtd_slot)
    requires usbtd_map_get_pid(globals1, usbtd_slot) == usbtd_map_get_pid(globals2, usbtd_slot)
    requires usbtd_map_get_type(globals1, usbtd_slot) == usbtd_map_get_type(globals2, usbtd_slot)
    requires TestBit(usbtd_map_get_flags(globals2, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
    requires usbtd_map_get_wimpdrv_slotid(globals1, usbtd_slot) == usbtd_map_get_wimpdrv_slotid(globals2, usbtd_slot)
    requires usbtd_map_get_usbpdev_slotid(globals1, usbtd_slot) == usbtd_map_get_usbpdev_slotid(globals2, usbtd_slot)
    requires usbtd_map_get_busid(globals1, usbtd_slot) == usbtd_map_get_busid(globals2, usbtd_slot)

    requires forall i :: usbtd_map_valid_slot_id(i) && i != usbtd_slot
                ==> p_usbtd_equal(globals1, globals2, i)
        // Requirement: USB TD content is unchanged
    
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info())
    
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)

    ensures forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != usbtd_slot &&
                TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
                (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QH32)
            ==> WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();
    
    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    forall i:uint32 | usbtd_map_valid_slot_id(i) && i != usbtd_slot &&
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QH32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i)
    {
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);

        assert new_usbtd_types == old_usbtd_types;

        var drv_slot := usbtd_map_get_wimpdrv_slotid(globals1, i);
        Lemma_WK_USBTD_Map_SecureGlobalVarValues_qh32_Properties(globals1, i);
        var drv_pid := wimpdrv_get_pid(globals1, drv_slot);
        assert p__usbtd_verify_qh32_step2_OnSuccessCheck(globals1, drv_pid.v, i);

        // Prove p__usbtd_verify_qh32_step2_OnSuccessCheck(new_globals, drv_pid.v, i);
        var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 4 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 5 * UINT32_BYTES);
        var next_qh_slot1:paddr := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var next_qtd_slot1:paddr := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot1:paddr := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qh_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
        var alt_next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

        var next_qh_slot2:paddr := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var next_qtd_slot2:paddr := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot2:paddr := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qh_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
        var alt_next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

        assert next_qh_slot1 == next_qh_slot2;
        assert next_qtd_slot1 == next_qtd_slot2;
        assert alt_next_qtd_slot1 == alt_next_qtd_slot2;
        assert next_qh_p_Tflag1 == next_qh_p_Tflag2;
        assert next_qtd_p_Tflag1 == next_qtd_p_Tflag2;
        assert alt_next_qtd_p_Tflag1 == alt_next_qtd_p_Tflag2;

        if(next_qh_p_Tflag1 != 1)
        {
            assert (0 <= next_qh_slot1 < USB_TD_ENTRY_NUM);

            if(next_qh_slot1 != usbtd_slot)
            {
                assert p_usbtd_equal(globals1, globals2, next_qh_slot1);
                assert usbtd_map_get_pid(globals1, next_qh_slot1) == usbtd_map_get_pid(globals2, next_qh_slot1);
                assert usbtd_map_get_flags(globals1, next_qh_slot1) == usbtd_map_get_flags(globals2, next_qh_slot1);

                assert usbtd_map_get_pid(globals2, next_qh_slot1) == drv_pid;
                assert TestBit(usbtd_map_get_flags(globals2, next_qh_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
            }
            else
            {
                assert usbtd_map_get_pid(globals2, next_qh_slot1) == drv_pid;
                assert TestBit(usbtd_map_get_flags(globals2, next_qh_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
            }
        }

        if(next_qtd_p_Tflag1 != 1)
        {
            assert (0 <= next_qtd_slot1 < USB_TD_ENTRY_NUM);

            if(next_qtd_slot1 != usbtd_slot)
            {
                assert p_usbtd_equal(globals1, globals2, next_qtd_slot1);
                assert usbtd_map_get_pid(globals1, next_qtd_slot1) == usbtd_map_get_pid(globals2, next_qtd_slot1);
                assert usbtd_map_get_flags(globals1, next_qtd_slot1) == usbtd_map_get_flags(globals2, next_qtd_slot1);

                assert usbtd_map_get_pid(globals2, next_qtd_slot1) == drv_pid;
                assert TestBit(usbtd_map_get_flags(globals2, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
            }
            else
            {
                assert usbtd_map_get_pid(globals2, next_qtd_slot1) == drv_pid;
                assert TestBit(usbtd_map_get_flags(globals2, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
            }
        }

        if(alt_next_qtd_p_Tflag1 != 1)
        {
            assert (0 <= alt_next_qtd_slot1 < USB_TD_ENTRY_NUM);

            if(alt_next_qtd_slot1 != usbtd_slot)
            {
                assert p_usbtd_equal(globals1, globals2, alt_next_qtd_slot1);
                assert usbtd_map_get_pid(globals1, alt_next_qtd_slot1) == usbtd_map_get_pid(globals2, alt_next_qtd_slot1);
                assert usbtd_map_get_flags(globals1, alt_next_qtd_slot1) == usbtd_map_get_flags(globals2, alt_next_qtd_slot1);

                assert usbtd_map_get_pid(globals2, alt_next_qtd_slot1) == drv_pid;
                assert TestBit(usbtd_map_get_flags(globals2, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
            }
            else
            {
                assert usbtd_map_get_pid(globals2, alt_next_qtd_slot1) == drv_pid;
                assert TestBit(usbtd_map_get_flags(globals2, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
            }
        }

        assert p__usbtd_verify_qh32_step2_OnSuccessCheck(globals2, drv_pid.v, i);

        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfMostFieldsOfSecureUSBTDsAreUnchanged(globals1, globals2, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i);
    }
}

// Lemma: If one USB TD (qTD32) is modified in flags/handle/input_params, and not have secure flag set at the end, 
// then all result qTD32s preserve WK_USBTD_Map_SecureGlobalVarValues_qTD32
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfOneUSBTDIsModified_AndModifyingUSBTDRemoveSecureSlotFlag_qtd32(
    globals1:globalsmap, globals2:globalsmap, usbtd_slot:uint32
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals2)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals2)
    
    requires usbtd_map_valid_slot_id(usbtd_slot)
    requires p_usbtd_content_equal(globals1, globals2, usbtd_slot)
    requires usbtd_map_get_pid(globals1, usbtd_slot) == usbtd_map_get_pid(globals2, usbtd_slot)
    requires usbtd_map_get_type(globals1, usbtd_slot) == usbtd_map_get_type(globals2, usbtd_slot)
    requires TestBit(usbtd_map_get_flags(globals2, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit) == false
    requires usbtd_map_get_wimpdrv_slotid(globals1, usbtd_slot) == usbtd_map_get_wimpdrv_slotid(globals2, usbtd_slot)
    requires usbtd_map_get_usbpdev_slotid(globals1, usbtd_slot) == usbtd_map_get_usbpdev_slotid(globals2, usbtd_slot)
    requires usbtd_map_get_busid(globals1, usbtd_slot) == usbtd_map_get_busid(globals2, usbtd_slot)

    requires forall i :: usbtd_map_valid_slot_id(i) && i != usbtd_slot
                ==> p_usbtd_equal(globals1, globals2, i)
        // Requirement: USB TD content is unchanged

    requires usbtds_verifiedtds_do_not_associate_usbtd(globals1, usbtd_slot)
        // Requirement: If the new flag has no SlotSecure set, then the USB TD must not be referenced by any 
        // verified/secure USB TDs
    
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info())
    
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)

    ensures forall i:uint32 :: usbtd_map_valid_slot_id(i) && 
                TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
                (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QTD32)
            ==> WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();
    
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

    forall i:uint32 | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i)
    {
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);

        assert new_usbtd_types == old_usbtd_types;

        var drv_slot := usbtd_map_get_wimpdrv_slotid(globals1, i);
        Lemma_WK_USBTD_Map_SecureGlobalVarValues_qTD32_Properties(globals1, i);
        var drv_pid := wimpdrv_get_pid(globals1, drv_slot);
        assert p__usbtd_verify_qtd32_step2_OnSuccessCheck(globals1, drv_pid.v, i);

        // Prove p__usbtd_verify_qtd32_step2_OnSuccessCheck(globals2, drv_pid.v, i)
        var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + UINT32_BYTES);
        var next_qtd_slot1:uint32 := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot1:uint32 := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var alt_next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

        var next_qtd_slot2:uint32 := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot2:uint32 := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var alt_next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + UINT32_BYTES), 0x1);

        assert next_qtd_slot1 == next_qtd_slot2;
        assert alt_next_qtd_slot1 == alt_next_qtd_slot2;
        assert next_qtd_p_Tflag1 == next_qtd_p_Tflag2;
        assert alt_next_qtd_p_Tflag1 == alt_next_qtd_p_Tflag2;

        if(i != usbtd_slot)
        {
            if(next_qtd_p_Tflag1 != 1)
            {
                assert (0 <= next_qtd_slot1 < USB_TD_ENTRY_NUM);

                if(next_qtd_slot1 != usbtd_slot)
                {
                    assert p_usbtd_equal(globals1, globals2, next_qtd_slot1);
                    assert usbtd_map_get_pid(globals1, next_qtd_slot1) == usbtd_map_get_pid(globals2, next_qtd_slot1);
                    assert usbtd_map_get_flags(globals1, next_qtd_slot1) == usbtd_map_get_flags(globals2, next_qtd_slot1);

                    assert usbtd_map_get_pid(globals2, next_qtd_slot1) == drv_pid;
                    assert TestBit(usbtd_map_get_flags(globals2, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
                }
                else
                {
                    assert usbtd_map_get_pid(globals2, next_qtd_slot1) == drv_pid;

                    assert TestBit(usbtd_map_get_flags(globals1, i), USBTD_SLOT_FLAG_SlotSecure_Bit);
                    assert usbtds_verifiedtds_do_not_associate_usbtd_qtd32(globals1, i, usbtd_slot);
                    reveal usbtds_verifiedtds_do_not_associate_usbtd_qtd32();
                    assert false;
                }
            }

            if(alt_next_qtd_p_Tflag1 != 1)
            {
                assert (0 <= alt_next_qtd_slot1 < USB_TD_ENTRY_NUM);

                if(alt_next_qtd_slot1 != usbtd_slot)
                {
                    assert p_usbtd_equal(globals1, globals2, alt_next_qtd_slot1);
                    assert usbtd_map_get_pid(globals1, alt_next_qtd_slot1) == usbtd_map_get_pid(globals2, alt_next_qtd_slot1);
                    assert usbtd_map_get_flags(globals1, alt_next_qtd_slot1) == usbtd_map_get_flags(globals2, alt_next_qtd_slot1);

                    assert usbtd_map_get_pid(globals2, alt_next_qtd_slot1) == drv_pid;
                    assert TestBit(usbtd_map_get_flags(globals2, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
                }
                else
                {
                    assert usbtd_map_get_pid(globals2, alt_next_qtd_slot1) == drv_pid;

                    assert TestBit(usbtd_map_get_flags(globals1, i), USBTD_SLOT_FLAG_SlotSecure_Bit);
                    assert usbtds_verifiedtds_do_not_associate_usbtd_qtd32(globals1, i, usbtd_slot);
                    reveal usbtds_verifiedtds_do_not_associate_usbtd_qtd32();
                    assert false;
                }
            }
    
            assert p__usbtd_verify_qtd32_step2_OnSuccessCheck(globals2, drv_pid.v, i);

            Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfUnrefedUSBTDIsModified(globals1, globals2, i, usbtd_slot);
            assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i);
        }
        else
        {
            assert TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) == false;
            assert false;
        }
    }
}

// Lemma: If one USB TD (qh32) is modified in flags/handle/input_params, and not have secure flag set at the end, 
// then all result qTD32s preserve WK_USBTD_Map_SecureGlobalVarValues_qTD32
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfOneUSBTDIsModified_AndModifyingUSBTDRemoveSecureSlotFlag_qh32(
    globals1:globalsmap, globals2:globalsmap, usbtd_slot:uint32
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals2)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals2)
    
    requires usbtd_map_valid_slot_id(usbtd_slot)
    requires p_usbtd_content_equal(globals1, globals2, usbtd_slot)
    requires usbtd_map_get_pid(globals1, usbtd_slot) == usbtd_map_get_pid(globals2, usbtd_slot)
    requires usbtd_map_get_type(globals1, usbtd_slot) == usbtd_map_get_type(globals2, usbtd_slot)
    requires TestBit(usbtd_map_get_flags(globals2, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit) == false
    requires usbtd_map_get_wimpdrv_slotid(globals1, usbtd_slot) == usbtd_map_get_wimpdrv_slotid(globals2, usbtd_slot)
    requires usbtd_map_get_usbpdev_slotid(globals1, usbtd_slot) == usbtd_map_get_usbpdev_slotid(globals2, usbtd_slot)
    requires usbtd_map_get_busid(globals1, usbtd_slot) == usbtd_map_get_busid(globals2, usbtd_slot)

    requires forall i :: usbtd_map_valid_slot_id(i) && i != usbtd_slot
                ==> p_usbtd_equal(globals1, globals2, i)
        // Requirement: USB TD content is unchanged

    requires usbtds_verifiedtds_do_not_associate_usbtd(globals1, usbtd_slot)
        // Requirement: If the new flag has no SlotSecure set, then the USB TD must not be referenced by any 
        // verified/secure USB TDs
    
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info())
    
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)

    ensures forall i:uint32 :: usbtd_map_valid_slot_id(i) && 
                TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
                (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QH32)
            ==> WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();
    
    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    forall i:uint32 | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QH32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i)
    {
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);

        assert new_usbtd_types == old_usbtd_types;

        var drv_slot := usbtd_map_get_wimpdrv_slotid(globals1, i);
        Lemma_WK_USBTD_Map_SecureGlobalVarValues_qh32_Properties(globals1, i);
        var drv_pid := wimpdrv_get_pid(globals1, drv_slot);
        assert p__usbtd_verify_qh32_step2_OnSuccessCheck(globals1, drv_pid.v, i);

        // Prove p__usbtd_verify_qh32_step2_OnSuccessCheck(new_globals, drv_pid.v, i);
        var td_vaddr:int := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 4 * UINT32_BYTES);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + 5 * UINT32_BYTES);
        var next_qh_slot1:paddr := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var next_qtd_slot1:paddr := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot1:paddr := RightShift(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qh_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
        var alt_next_qtd_p_Tflag1:uint32 := BitwiseAnd(global_read_uint32(globals1, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

        var next_qh_slot2:paddr := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var next_qtd_slot2:paddr := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS); 
        var alt_next_qtd_slot2:paddr := RightShift(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), USBTD_Link_NextUSBTD_SHIFT_BITS);
        var next_qh_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr), 0x1);
        var next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 4 * UINT32_BYTES), 0x1);
        var alt_next_qtd_p_Tflag2:uint32 := BitwiseAnd(global_read_uint32(globals2, G_USBTD_MAP_MEM(), td_vaddr + 5 * UINT32_BYTES), 0x1);

        assert next_qh_slot1 == next_qh_slot2;
        assert next_qtd_slot1 == next_qtd_slot2;
        assert alt_next_qtd_slot1 == alt_next_qtd_slot2;
        assert next_qh_p_Tflag1 == next_qh_p_Tflag2;
        assert next_qtd_p_Tflag1 == next_qtd_p_Tflag2;
        assert alt_next_qtd_p_Tflag1 == alt_next_qtd_p_Tflag2;

        if(i != usbtd_slot)
        {
            if(next_qh_p_Tflag1 != 1)
            {
                assert (0 <= next_qh_slot1 < USB_TD_ENTRY_NUM);

                if(next_qh_slot1 != usbtd_slot)
                {
                    assert p_usbtd_equal(globals1, globals2, next_qh_slot1);
                    assert usbtd_map_get_pid(globals1, next_qh_slot1) == usbtd_map_get_pid(globals2, next_qh_slot1);
                    assert usbtd_map_get_flags(globals1, next_qh_slot1) == usbtd_map_get_flags(globals2, next_qh_slot1);

                    assert usbtd_map_get_pid(globals2, next_qh_slot1) == drv_pid;
                    assert TestBit(usbtd_map_get_flags(globals2, next_qh_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
                }
                else
                {
                    assert usbtd_map_get_pid(globals2, next_qh_slot1) == drv_pid;

                    assert TestBit(usbtd_map_get_flags(globals1, i), USBTD_SLOT_FLAG_SlotSecure_Bit);
                    assert usbtds_verifiedtds_do_not_associate_usbtd_qh32(globals1, i, usbtd_slot);
                    reveal usbtds_verifiedtds_do_not_associate_usbtd_qh32();
                    assert false;
                }
            }

            if(next_qtd_p_Tflag1 != 1)
            {
                assert (0 <= next_qtd_slot1 < USB_TD_ENTRY_NUM);

                if(next_qtd_slot1 != usbtd_slot)
                {
                    assert p_usbtd_equal(globals1, globals2, next_qtd_slot1);
                    assert usbtd_map_get_pid(globals1, next_qtd_slot1) == usbtd_map_get_pid(globals2, next_qtd_slot1);
                    assert usbtd_map_get_flags(globals1, next_qtd_slot1) == usbtd_map_get_flags(globals2, next_qtd_slot1);

                    assert usbtd_map_get_pid(globals2, next_qtd_slot1) == drv_pid;
                    assert TestBit(usbtd_map_get_flags(globals2, next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
                }
                else
                {
                    assert usbtd_map_get_pid(globals2, next_qtd_slot1) == drv_pid;

                    assert TestBit(usbtd_map_get_flags(globals1, i), USBTD_SLOT_FLAG_SlotSecure_Bit);
                    assert usbtds_verifiedtds_do_not_associate_usbtd_qh32(globals1, i, usbtd_slot);
                    reveal usbtds_verifiedtds_do_not_associate_usbtd_qh32();
                    assert false;
                }
            }

            if(alt_next_qtd_p_Tflag1 != 1)
            {
                assert (0 <= alt_next_qtd_slot1 < USB_TD_ENTRY_NUM);

                if(alt_next_qtd_slot1 != usbtd_slot)
                {
                    assert p_usbtd_equal(globals1, globals2, alt_next_qtd_slot1);
                    assert usbtd_map_get_pid(globals1, alt_next_qtd_slot1) == usbtd_map_get_pid(globals2, alt_next_qtd_slot1);
                    assert usbtd_map_get_flags(globals1, alt_next_qtd_slot1) == usbtd_map_get_flags(globals2, alt_next_qtd_slot1);

                    assert usbtd_map_get_pid(globals2, alt_next_qtd_slot1) == drv_pid;
                    assert TestBit(usbtd_map_get_flags(globals2, alt_next_qtd_slot1), USBTD_SLOT_FLAG_SlotSecure_Bit);
                }
                else
                {
                    assert usbtd_map_get_pid(globals2, alt_next_qtd_slot1) == drv_pid;

                    assert TestBit(usbtd_map_get_flags(globals1, i), USBTD_SLOT_FLAG_SlotSecure_Bit);
                    assert usbtds_verifiedtds_do_not_associate_usbtd_qh32(globals1, i, usbtd_slot);
                    reveal usbtds_verifiedtds_do_not_associate_usbtd_qh32();
                    assert false;
                }
            }
    
            assert p__usbtd_verify_qh32_step2_OnSuccessCheck(globals2, drv_pid.v, i);
            
            Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfUnrefedUSBTDIsModified(globals1, globals2, i, usbtd_slot);
            assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i);
        }
        else
        {
            assert TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) == false;
            assert false;
        }
    }
}




/*********************** Private Lemmas - Lemma_SecureObjsAddrs_MemSeparation_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged ********************/
// Lemma: On <s.object> modification, If ObjIDs are unchanged, then WK_SecureObjsAddrs_MemSeparation holds
lemma Lemma_SecureObjsAddrs_MemSeparation_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
    
    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires s.wk_mstate == s'.wk_mstate
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: id in s'.objects.os_tds
                ==> s.objects.os_tds[id].pid == s'.objects.os_tds[id].pid
    requires forall id :: id in s'.objects.os_fds
                ==> s.objects.os_fds[id].pid == s'.objects.os_fds[id].pid
    requires forall id :: id in s'.objects.os_dos
                ==> s.objects.os_dos[id].pid == s'.objects.os_dos[id].pid
        // Requirement: OS objects' PIDs are unchanged

    ensures WK_SecureObjsAddrs_MemSeparation(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();

    Lemma_SecureObjsAddrs_MemSeparation_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged_OSTDs(s, s');
    Lemma_SecureObjsAddrs_MemSeparation_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged_OSFDs(s, s');
    Lemma_SecureObjsAddrs_MemSeparation_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged_OSDOs(s, s');
}

// Lemma: On <s.object> modification, If ObjIDs are unchanged, then WK_SecureObjsAddrs_MemSeparation holds for OS TDs
lemma Lemma_SecureObjsAddrs_MemSeparation_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged_OSTDs(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
    
    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires s.wk_mstate == s'.wk_mstate
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: id in s'.objects.os_tds
                ==> s.objects.os_tds[id].pid == s'.objects.os_tds[id].pid
    requires forall id :: id in s'.objects.os_fds
                ==> s.objects.os_fds[id].pid == s'.objects.os_fds[id].pid
    requires forall id :: id in s'.objects.os_dos
                ==> s.objects.os_dos[id].pid == s'.objects.os_dos[id].pid
        // Requirement: OS objects' PIDs are unchanged

    ensures var subjs' := s'.subjects;
            var objs' := s'.objects;
            var id_mappings' := s'.id_mappings;
            var objs_addrs' := s'.objs_addrs;
            var globals' := wkm_get_globals(s'.wk_mstate);
            forall os_obj_id:TD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 :: 
            WSM_IsOSTDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS TD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.tds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
                ==> (   
                        pmem1.paddr_start <= pmem1.paddr_end && pmem2.paddr_start <= pmem2.paddr_end && 
                        !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
                    )
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();

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

    Lemma_WSM_ObjPID_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged(s, s');
    forall os_obj_id:TD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSTDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS TD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.tds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsOSTDID(objs, os_obj_id) == WSM_IsOSTDID(objs', os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);
    }
}

// Lemma: On <s.object> modification, If ObjIDs are unchanged, then WK_SecureObjsAddrs_MemSeparation holds for OS FDs
lemma Lemma_SecureObjsAddrs_MemSeparation_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged_OSFDs(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
    
    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires s.wk_mstate == s'.wk_mstate
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: id in s'.objects.os_tds
                ==> s.objects.os_tds[id].pid == s'.objects.os_tds[id].pid
    requires forall id :: id in s'.objects.os_fds
                ==> s.objects.os_fds[id].pid == s'.objects.os_fds[id].pid
    requires forall id :: id in s'.objects.os_dos
                ==> s.objects.os_dos[id].pid == s'.objects.os_dos[id].pid
        // Requirement: OS objects' PIDs are unchanged

    ensures var subjs' := s'.subjects;
            var objs' := s'.objects;
            var id_mappings' := s'.id_mappings;
            var objs_addrs' := s'.objs_addrs;
            var globals' := wkm_get_globals(s'.wk_mstate);
            forall os_obj_id:FD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 :: 
            WSM_IsOSFDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.fds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
                ==> (   
                        pmem1.paddr_start <= pmem1.paddr_end && pmem2.paddr_start <= pmem2.paddr_end && 
                        !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
                    )
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();

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

    Lemma_WSM_ObjPID_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged(s, s');
    forall os_obj_id:FD_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSFDID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.fds_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsOSFDID(objs, os_obj_id) == WSM_IsOSFDID(objs', os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);
    }
}

// Lemma: On <s.object> modification, If ObjIDs are unchanged, then WK_SecureObjsAddrs_MemSeparation holds for OS DOs
lemma Lemma_SecureObjsAddrs_MemSeparation_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged_OSDOs(s:state, s':state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))
    
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)
    requires WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
    
    requires WK_SecureObjsAddrs_MemSeparation(s.subjects, s.objects, s.id_mappings, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires s.wk_mstate == s'.wk_mstate
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: id in s'.objects.os_tds
                ==> s.objects.os_tds[id].pid == s'.objects.os_tds[id].pid
    requires forall id :: id in s'.objects.os_fds
                ==> s.objects.os_fds[id].pid == s'.objects.os_fds[id].pid
    requires forall id :: id in s'.objects.os_dos
                ==> s.objects.os_dos[id].pid == s'.objects.os_dos[id].pid
        // Requirement: OS objects' PIDs are unchanged

    ensures var subjs' := s'.subjects;
            var objs' := s'.objects;
            var id_mappings' := s'.id_mappings;
            var objs_addrs' := s'.objs_addrs;
            var globals' := wkm_get_globals(s'.wk_mstate);
            forall os_obj_id:DO_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 :: 
            WSM_IsOSDOID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.dos_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
                ==> (   
                        pmem1.paddr_start <= pmem1.paddr_end && pmem2.paddr_start <= pmem2.paddr_end && 
                        !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
                    )
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();

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

    Lemma_WSM_ObjPID_OnObjectModification_IfObjIDsAndOSObjsPIDsAreUnchanged(s, s');
    forall os_obj_id:DO_ID, wimpdrv_do_id:DO_ID, pmem1, pmem2 | 
            WSM_IsOSDOID(objs', os_obj_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid) &&   // Active OS FD
            WSM_IsWimpDrvDOID(objs', wimpdrv_do_id) && WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid) && // Active WimpDrv's DO
            pmem1 in objs_addrs'.dos_addrs[os_obj_id].paddrs && pmem2 in objs_addrs'.dos_addrs[wimpdrv_do_id].paddrs
        ensures !is_mem_region_overlap(pmem1.paddr_start, pmem1.paddr_end, pmem2.paddr_start, pmem2.paddr_end)
    {
        assert WSM_IsOSDOID(objs, os_obj_id) == WSM_IsOSDOID(objs', os_obj_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, os_obj_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', os_obj_id.oid);
        assert WSM_IsWimpDrvDOID(objs, wimpdrv_do_id) == WSM_IsWimpDrvDOID(objs', wimpdrv_do_id);
        assert WSM_IsActiveObj(subjs, objs, id_mappings, globals, wimpdrv_do_id.oid) == WSM_IsActiveObj(subjs', objs', id_mappings', globals', wimpdrv_do_id.oid);
    }
}