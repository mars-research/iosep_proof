include "usb_pdev.i.dfy"

/*********************** Axioms ********************/
// [HW] Axiom (well known): USBPDevs do not define transfers to any TDs
lemma {:axiom} Lemma_USBPDev_HCodedTDDoNotDefineTransferToTDs(s:state, usbpdev_id:Dev_ID)
    requires ValidState(s)
    requires usbpdev_id in s.subjects.usbpdevs

    requires s.subjects.usbpdevs[usbpdev_id].hcoded_td_id in s.objects.usbpdev_tds
        // Properties needed by the following properties
    ensures forall hcoded_td_id :: hcoded_td_id == s.subjects.usbpdevs[usbpdev_id].hcoded_td_id
                ==> MapGetKeys(s.objects.usbpdev_tds[hcoded_td_id].trans_params_tds) == {}




/*********************** Lemmas ********************/
lemma Lemma_WK_ValidGlobalVarValues_USBPDevs_HoldIfWrittingUpdateFlagField_WriteToUpdating(
    s:state, s':state, slot:word
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))
    requires global_read_fullval(wkm_get_globals(s.wk_mstate), G_WimpUSBPDev_DevList()) == 
             global_read_fullval(wkm_get_globals(s'.wk_mstate), G_WimpUSBPDev_DevList())

    requires usbpdev_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            wkm_get_globals(s'.wk_mstate) == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpUSBPDev_Info(), vaddr1, WimpUSBPDev_Slot_UpdateFlag_Updating)
    requires WK_ValidGlobalVarValues_USBPDevs(s.subjects, wkm_get_globals(s.wk_mstate))

    requires s'.subjects == s.subjects

    ensures WK_ValidGlobalVarValues_USBPDevs(s'.subjects, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidGlobalVarValues_USBPDevs();
}

// Lemma: After writting <low_addr> field of a slot in <g_wimpdevs_info>, the new global variable  
// satisfies WK_ValidGlobalVarValues_USBPDevs
lemma Lemma_WK_ValidGlobalVarValues_USBPDevs_HoldIfWrittingLowAddrField(
    s:state, s':state, slot:word, new_v:word
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))

    requires usbpdev_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            wkm_get_globals(s'.wk_mstate) == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpUSBPDev_Info(), vaddr1, new_v)
    
    requires usbpdev_get_updateflag(wkm_get_globals(s.wk_mstate), slot) == WimpUSBPDev_Slot_UpdateFlag_Updating
    requires WK_ValidGlobalVarValues_USBPDevs(s.subjects, wkm_get_globals(s.wk_mstate))

    requires s'.subjects == s.subjects

    ensures WK_ValidGlobalVarValues_USBPDevs(s'.subjects, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidGlobalVarValues_USBPDevs();
}

// Lemma: After writting <high_addr> field of a slot in <g_wimpdevs_info>, the new global variable  
// satisfies WK_ValidGlobalVarValues_USBPDevs
lemma Lemma_WK_ValidGlobalVarValues_USBPDevs_HoldIfWrittingHighAddrField(
    s:state, s':state, slot:word, new_v:word
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))

    requires usbpdev_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            wkm_get_globals(s'.wk_mstate) == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpUSBPDev_Info(), vaddr1, new_v)
    
    requires usbpdev_get_updateflag(wkm_get_globals(s.wk_mstate), slot) == WimpUSBPDev_Slot_UpdateFlag_Updating
    requires WK_ValidGlobalVarValues_USBPDevs(s.subjects, wkm_get_globals(s.wk_mstate))

    requires s'.subjects == s.subjects

    ensures WK_ValidGlobalVarValues_USBPDevs(s'.subjects, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidGlobalVarValues_USBPDevs();
}

// Lemma: After writting <update_flag> field of a slot in <g_wimpdevs_info>, the new global variable satisfies 
// WK_ValidGlobalVarValues_USBPDevs
lemma Lemma_WK_ValidGlobalVarValues_USBPDevs_HoldIfWrittingUpdateFlagField_WriteToUpdateComplete(
    s:state, s':state, slot:word
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))

    requires usbpdev_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            wkm_get_globals(s'.wk_mstate) == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpUSBPDev_Info(), vaddr1, WimpUSBPDev_Slot_UpdateFlag_Complete)

    requires var globals := wkm_get_globals(s.wk_mstate);
             usbpdev_get_pid(globals, slot) != WS_PartitionID(PID_INVALID) 
                ==> (
                        var usbpdev_addr_raw:uint64 := usbpdev_get_addr(globals, slot);
                        var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);

                        usbpdev_addr in usbpdevlist_get_all_non_empty_addrs(globals)
                    )
        // Requirement: If the updating USBPDev slot records an active PID, then the new USBPDev addr must be in 
        // <g_wimpdevs_devlist>
             
    requires WK_ValidGlobalVarValues_USBPDevs(s.subjects, wkm_get_globals(s.wk_mstate))

    requires s'.subjects == s.subjects

    ensures WK_ValidGlobalVarValues_USBPDevs(s'.subjects, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidGlobalVarValues_USBPDevs();
}

// Lemma: After writting <pid> field of a slot in <g_wimpdevs_info> to be PID_INVALID, the new global variable  
// satisfies WK_ValidGlobalVarValues_USBPDevs
lemma Lemma_WK_ValidGlobalVarValues_USBPDevs_HoldIfWrittingPIDField_NewPIDIsInvalid(
    s:state, s':state, slot:word, new_v:word
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))

    requires 0 <= slot < WimpUSBPDev_Info_ENTRIES
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            wkm_get_globals(s'.wk_mstate) == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpUSBPDev_Info(), vaddr1, new_v)

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
        // Requirement: USBPDevs in the model/system must have <active_in_os> to be false
    
    requires new_v == PID_INVALID
    requires WK_ValidGlobalVarValues_USBPDevs(s.subjects, wkm_get_globals(s.wk_mstate))

    requires s'.subjects == s.subjects

    ensures WK_ValidGlobalVarValues_USBPDevs(s'.subjects, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidGlobalVarValues_USBPDevs();
}

// Lemma: After writting <pid> field of a slot in <g_wimpdevs_info> to be PID_VALID, the new global variable  
// satisfies WK_ValidGlobalVarValues_USBPDevs
lemma Lemma_WK_ValidGlobalVarValues_USBPDevs_HoldIfWrittingPIDField_NewPIDIsValid(
    s:state, s':state, slot:word, new_v:word
)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidGlobalState(wkm_get_globals(s'.wk_mstate))

    requires 0 <= slot < WimpUSBPDev_Info_ENTRIES
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            wkm_get_globals(s'.wk_mstate) == global_write_word(wkm_get_globals(s.wk_mstate), G_WimpUSBPDev_Info(), vaddr1, new_v)

    requires forall usbpdev_id:Dev_ID :: WSM_IsUSBPDevID(s.subjects, usbpdev_id)
            ==> s.subjects.usbpdevs[usbpdev_id].active_in_os == false
        // Requirement: USBPDevs in the model/system must have <active_in_os> to be false
    requires var globals := wkm_get_globals(s.wk_mstate);
             var usbpdev_addr_raw:uint64 := usbpdev_get_addr(globals, slot);
             usb_is_usbpdev_addr_valid(usbpdev_addr_raw) &&
             var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
             usbpdev_addr in usbpdevlist_get_all_non_empty_addrs(globals)
        // Requirement: The USBPDev addr stored at <slot> must be in <g_wimpdevs_devlist>
        
    requires new_v != PID_INVALID
    requires WK_ValidGlobalVarValues_USBPDevs(s.subjects, wkm_get_globals(s.wk_mstate))

    requires s'.subjects == s.subjects

    ensures WK_ValidGlobalVarValues_USBPDevs(s'.subjects, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidGlobalVarValues_USBPDevs();

    var globals := wkm_get_globals(s.wk_mstate);
    var globals' := wkm_get_globals(s'.wk_mstate);

    Lemma_WimpUSBPDev_PreserveOtherSlotsIfModifyingOneSlot(globals, globals', slot, WimpUSBPDev_Info_ENTRY_PID_ByteOffset, new_v);
    forall i | usbpdev_valid_slot_id(i) &&
            usbpdev_get_pid(globals', i) != WS_PartitionID(PID_INVALID) &&
            usbpdev_get_updateflag(globals', i) == WimpUSBPDev_Slot_UpdateFlag_Complete
        ensures (
                var usbpdev_addr_raw:uint64 := usbpdev_get_addr(globals', i);
                var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);

                usbpdev_addr in usbpdevlist_get_all_non_empty_addrs(globals')
            )
    {
        var usbpdev_addr_raw:uint64 := usbpdev_get_addr(globals', i);
        var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);

        if(i != slot)
        {
            assert p_usbpdev_slot_equal(globals, globals', i);
            reveal p_usbpdev_slot_equal();

            assert usbpdev_addr in usbpdevlist_get_all_non_empty_addrs(globals');
        }
        else
        {
            assert usbpdev_addr in usbpdevlist_get_all_non_empty_addrs(globals');
        }
    }
}