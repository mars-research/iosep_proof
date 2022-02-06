include "usb_tds_checks.s.dfy"

// Lemma: If the secure USB TDs are unchanged, and the given USB TD is secure, then Is_USBTD_NotModifyUSBPDevsAddrs holds
lemma Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(
    globals1:globalsmap, globals2:globalsmap, td_slot:word
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)

    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(td_slot)

    requires forall i:uint32 :: usbtd_map_valid_slot_id(i) && 
                    TestBit(usbtd_map_get_flags(globals1, i), USBTD_SLOT_FLAG_SlotSecure_Bit)
                ==> p_usbtd_equal(globals1, globals2, i)
        // Requirement: Secure USB TDs are unchanged
    requires TestBit(usbtd_map_get_flags(globals1, td_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
        // Requirement: The USB TD <td_slot> is secure

    requires Is_USBTD_NotModifyUSBPDevsAddrs(globals1, td_slot)
    ensures Is_USBTD_NotModifyUSBPDevsAddrs(globals2, td_slot)
{
    reveal p_usbtd_equal();
    Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfMostFieldsOfSecureUSBTDsAreUnchanged(globals1, globals2, td_slot);
}

lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_qTD32_Properties(globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals)

    requires usbtd_map_valid_slot_id(td_slot)

    requires WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals, td_slot)

    ensures var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, td_slot);
            wimpdrv_valid_slot_id(drv_slot)
{
    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, td_slot);
    assert usbtd_slot_valid_wimpdrv_slotid(globals, td_slot);
    assert wimpdrv_valid_slot_id(drv_slot);
}

lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_qh32_Properties(globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals)

    requires usbtd_map_valid_slot_id(td_slot)

    requires WK_USBTD_Map_SecureGlobalVarValues_qh32(globals, td_slot)

    ensures var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, td_slot);
            wimpdrv_valid_slot_id(drv_slot)
{
    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, td_slot);
    assert usbtd_slot_valid_wimpdrv_slotid(globals, td_slot);
    assert wimpdrv_valid_slot_id(drv_slot);
}

// [TODO] Not support iTD and siTD yet
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_iTD32_Properties(globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals)

    requires usbtd_map_valid_slot_id(td_slot)

    requires WK_USBTD_Map_SecureGlobalVarValues_iTD32(globals, td_slot)

    ensures var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, td_slot);
            wimpdrv_valid_slot_id(drv_slot)
{
    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, td_slot);
    assert usbtd_slot_valid_wimpdrv_slotid(globals, td_slot);
    assert wimpdrv_valid_slot_id(drv_slot);
}

// [TODO] Not support iTD and siTD yet
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_siTD32_Properties(globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals)

    requires usbtd_map_valid_slot_id(td_slot)

    requires WK_USBTD_Map_SecureGlobalVarValues_siTD32(globals, td_slot)

    ensures var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, td_slot);
            wimpdrv_valid_slot_id(drv_slot)
{
    var drv_slot := usbtd_map_get_wimpdrv_slotid(globals, td_slot);
    assert usbtd_slot_valid_wimpdrv_slotid(globals, td_slot);
    assert wimpdrv_valid_slot_id(drv_slot);
}

// Lemma: If G_USBTD_MAP_MEM, G_WimpDrvs_Info, and G_WimpUSBPDev_Info are unchanged, then 
// <WK_USBTD_Map_SecureGlobalVarValues> holds
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfUSBTDsAndWimpDrvsAndUSBPDevsAreUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals2)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals2)
    
    requires global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM())
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info())
    
    ensures WK_USBTD_Map_SecureGlobalVarValues(globals2)
{
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    forall i | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i)
    {
        var new_usbtd_flags := usbtd_map_get_flags(globals2, i);
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_flags := usbtd_map_get_flags(globals1, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;

        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals1, i);

        Lemma_SameUSBTDMem_Property(globals1, globals2);
        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(globals1, globals2, i);
    }

    forall i | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QH32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i)
    {
        var new_usbtd_flags := usbtd_map_get_flags(globals2, i);
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_flags := usbtd_map_get_flags(globals1, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;

        assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals1, i);

        Lemma_SameUSBTDMem_Property(globals1, globals2);
        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(globals1, globals2, i);
    }
}

// Lemma: If G_USBTD_MAP_MEM, G_WimpDrvs_Info, and G_WimpUSBPDev_Info are unchanged, then 
// <WK_USBTD_Map_SecureGlobalVarValues> holds
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfMostUSBTDsFieldAndWimpDrvsAndUSBPDevsAreUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals2)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals2)
    
    //requires global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM())
    requires forall i :: usbtd_map_valid_slot_id(i)
                ==> p_usbtd_content_equal(globals1, globals2, i)
    requires forall i :: usbtd_map_valid_slot_id(i)
                ==> usbtd_map_get_pid(globals1, i) == usbtd_map_get_pid(globals2, i)
    requires forall i :: usbtd_map_valid_slot_id(i)
                ==> usbtd_map_get_type(globals1, i) == usbtd_map_get_type(globals2, i)
    requires forall i :: usbtd_map_valid_slot_id(i)
                ==> usbtd_map_get_flags(globals1, i) == usbtd_map_get_flags(globals2, i)
    requires forall i :: usbtd_map_valid_slot_id(i)
                ==> usbtd_map_get_wimpdrv_slotid(globals1, i) == usbtd_map_get_wimpdrv_slotid(globals2, i)
    requires forall i :: usbtd_map_valid_slot_id(i)
                ==> usbtd_map_get_usbpdev_slotid(globals1, i) == usbtd_map_get_usbpdev_slotid(globals2, i)
    requires forall i :: usbtd_map_valid_slot_id(i)
                ==> usbtd_map_get_busid(globals1, i) == usbtd_map_get_busid(globals2, i)
        // Requirement: USB TD content is unchanged
    
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info())
    
    ensures WK_USBTD_Map_SecureGlobalVarValues(globals2)
{
    reveal p_usbtd_content_equal();
    
    reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qtd32_step4_OnSuccessCheck();

    reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step4_OnSuccessCheck();

    forall i | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QTD32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals2, i)
    {
        var new_usbtd_flags := usbtd_map_get_flags(globals2, i);
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_flags := usbtd_map_get_flags(globals1, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;

        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals1, i);
        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfMostFieldsOfSecureUSBTDsAreUnchanged(globals1, globals2, i);
    }

    forall i | usbtd_map_valid_slot_id(i) && 
            TestBit(usbtd_map_get_flags(globals2, i), USBTD_SLOT_FLAG_SlotSecure_Bit) &&
            (usbtd_map_get_type(globals2, i) == USBTDs_TYPE_QH32)
        ensures WK_USBTD_Map_SecureGlobalVarValues_qh32(globals2, i)
    {
        var new_usbtd_flags := usbtd_map_get_flags(globals2, i);
        var new_usbtd_types := usbtd_map_get_type(globals2, i);
        var old_usbtd_flags := usbtd_map_get_flags(globals1, i);
        var old_usbtd_types := usbtd_map_get_type(globals1, i);

        assert new_usbtd_flags == old_usbtd_flags;
        assert new_usbtd_types == old_usbtd_types;

        assert WK_USBTD_Map_SecureGlobalVarValues_qh32(globals1, i);
        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfMostFieldsOfSecureUSBTDsAreUnchanged(globals1, globals2, i);
    }
}