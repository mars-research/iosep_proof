include "usb_tds.i.dfy"
include "../../state_properties_validity.i.dfy"

// Lemma: When updating <id> field in a USB TD, if the new ID is good (i.e., either invalid or unique, <= USB TD ID 
// counter, and if active then the new ID must be valid), and WK_USBTD_Map_ValidGlobalVarValues(globals1), Then 
// WK_USBTD_Map_ValidGlobalVarValues(globals2)
lemma Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfNewIDOfSlotIsGood(
    s:state, s':state, slot:uint32, id_vaddr:vaddr, new_id:word
)
    requires ValidState(s)

    //requires WK_ValidMState(s'.wk_mstate)
    requires var globals' := wkm_get_globals(s'.wk_mstate);
             WK_ValidGlobalVars_Decls(globals')
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)

    requires usbtd_map_valid_slot_id(slot)
    requires id_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset

    requires is_valid_vaddr(id_vaddr)
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), id_vaddr)
    requires var globals1 := wkm_get_globals(s.wk_mstate);
             forall i :: usbtd_map_valid_slot_id(i) && i != slot &&
                    usbtd_map_get_idword(globals1, i) != USBTD_ID_INVALID
                ==> usbtd_map_get_idword(globals1, i) != new_id
        // Requirement: The new ID must be either invalid or unique
    requires var globals1 := wkm_get_globals(s.wk_mstate);
             new_id <= usbtd_id_counter_read(wkm_get_globals(s.wk_mstate)) &&
             (usbtd_map_get_pid(globals1, slot) != WS_PartitionID(PID_INVALID)
                ==> new_id != USBTD_ID_INVALID)
        // Requirement: The new ID must <= USB TD ID counter, and if active then the new ID must be valid

    requires WK_USBTD_Map_ValidGlobalVarValues(wkm_get_globals(s.wk_mstate))
    requires wkm_get_globals(s'.wk_mstate) == global_write_word(wkm_get_globals(s.wk_mstate), G_USBTD_MAP_MEM(), id_vaddr, new_id)

    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged

    ensures WK_USBTD_Map_ValidGlobalVarValues(wkm_get_globals(s'.wk_mstate))
{
    var globals1 := wkm_get_globals(s.wk_mstate);
    var globals2 := wkm_get_globals(s'.wk_mstate);

    forall i:uint32, j:uint32 | usbtd_map_valid_slot_id(i) && usbtd_map_valid_slot_id(j) &&
            usbtd_map_get_idword(globals2, i) != USBTD_ID_INVALID && usbtd_map_get_idword(globals2, j) != USBTD_ID_INVALID
        ensures usbtd_map_get_idword(globals2, i) == usbtd_map_get_idword(globals2, j) <==> i == j
    {
        var old_id_i := usbtd_map_get_idword(globals1, i);
        var new_id_i := usbtd_map_get_idword(globals2, i);
        var cur_id_vaddr_i := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset;
        var old_id_j := usbtd_map_get_idword(globals1, j);
        var new_id_j := usbtd_map_get_idword(globals2, j);
        var cur_id_vaddr_j := AddressOfGlobal(G_USBTD_MAP_MEM()) + j * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset;

        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_ID_BytesOffset);
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(j, G_USBTDs_MAP_ENTRY_ID_BytesOffset);
        if(cur_id_vaddr_i != id_vaddr && cur_id_vaddr_j != id_vaddr)
        {
            assert old_id_i == new_id_i;
            assert old_id_j == new_id_j;
        }
        else if (cur_id_vaddr_i == id_vaddr && cur_id_vaddr_j != id_vaddr)
        {
            assert old_id_j == new_id_j;
            assert new_id_i == new_id;
        }
        else if (cur_id_vaddr_i != id_vaddr && cur_id_vaddr_j == id_vaddr)
        {
            assert cur_id_vaddr_i != id_vaddr;
            assert cur_id_vaddr_j == id_vaddr;

            assert old_id_i == new_id_i;
            assert new_id_j == new_id;
        }
        else
        {
            assert cur_id_vaddr_i == id_vaddr;
            assert cur_id_vaddr_j == id_vaddr;

            assert new_id_j == new_id_i;

            Lemma_usbtd_slot_offset_UniquePairForVAddr();
            assert i == j;
        }
    }

    forall i | 0 <= i < USB_TD_ENTRY_NUM 
        ensures usbtd_slot_valid_id(globals2, i)
    {
        var old_id_i := usbtd_map_get_idword(globals1, i);
        var new_id_i := usbtd_map_get_idword(globals2, i);
        var cur_id_vaddr_i := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset;

        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_ID_BytesOffset);
        if(cur_id_vaddr_i != id_vaddr)
        {
            assert old_id_i == new_id_i;
            assert usbtd_slot_valid_id(globals1, i);
            assert usbtd_slot_valid_id(globals2, i);
        }
        else
        {
            assert usbtd_map_get_idword(globals2, i) == new_id;
            assert usbtd_slot_valid_id(globals2, i);
        }
    }

    // Prove forall i :: usbtd_map_valid_slot_id(i) ==> usbtd_map_get_idword(globals1, i) <= usbtd_id_counter_read(globals1);
    assert WK_USBTD_Map_ValidGlobalVarValues(globals1);
    Lemma_WK_USBTD_Map_ValidGlobalVarValues_P1_Equivilant(globals1);

    // Prove pre-conditions for Lemma_ValidState_ImpliesWK_ValidGlobalVarValues_ActiveUSBTDs
    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, new_id);
    reveal p_usbtd_equal();
    forall i | usbtd_map_valid_slot_id(i)
        ensures usbtd_map_get_idword(globals2, i) <= usbtd_id_counter_read(globals2) ||
                usbtd_map_get_idword(globals2, i) == USBTD_ID_INVALID
    {
        assert usbtd_id_counter_read(globals1) == usbtd_id_counter_read(globals2);
        if(i != slot)
        {
            assert usbtd_map_get_idword(globals1, i) == usbtd_map_get_idword(globals2, i);
        }
        else
        {
            assert usbtd_map_get_idword(globals2, i) == new_id;
        }
    }

    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, new_id);
    Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, new_id);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, new_id);
    Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, new_id);
    Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_ID_BytesOffset, new_id);

    Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(globals1, globals2);

    Lemma_ValidState_ImpliesWK_ValidGlobalVarValues_ActiveUSBTDs(s'.subjects, s'.objects, s'.id_mappings, globals2);
    reveal WK_ValidGlobalVarValues_ActiveUSBTDs();
}

// Lemma: When updating <pid> field in a USB TD, if the new PID is good (i.e., either invalid or fulfill 
// <pids_is_existing_wimp_pid>, and if new PID is valid then the current USB TD ID must be valid), 
// and WK_USBTD_Map_ValidGlobalVarValues(globals1), Then WK_USBTD_Map_ValidGlobalVarValues(globals2)
lemma Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfNewPIDOfSlotIsGood(
    s:state, s':state, slot:uint32, pid_vaddr:vaddr, new_pid:word
)
    requires ValidState(s)

    requires var globals' := wkm_get_globals(s'.wk_mstate);
             WK_ValidGlobalVars_Decls(globals')
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects)

    requires usbtd_map_valid_slot_id(slot)
    requires pid_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset

    requires is_valid_vaddr(pid_vaddr)
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), pid_vaddr)
    requires new_pid == PID_INVALID || pids_is_existing_wimp_pid(wkm_get_globals(s.wk_mstate), new_pid)
        // Requirement: The new PID must be either invalid or fulfill <pids_is_existing_wimp_pid>
    requires var globals := wkm_get_globals(s.wk_mstate);
             new_pid != PID_INVALID
                ==> usbtd_map_get_idword(globals, slot) != USBTD_ID_INVALID
        // Requirement: If the new PID is valid, then the current USB TD ID must be valid

    requires WK_USBTD_Map_ValidGlobalVarValues(wkm_get_globals(s.wk_mstate))
    requires wkm_get_globals(s'.wk_mstate) == global_write_word(wkm_get_globals(s.wk_mstate), G_USBTD_MAP_MEM(), pid_vaddr, new_pid)

    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged

    ensures WK_USBTD_Map_ValidGlobalVarValues(wkm_get_globals(s'.wk_mstate))
{
    var globals1 := wkm_get_globals(s.wk_mstate);
    var globals2 := wkm_get_globals(s'.wk_mstate);

    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures (usbtd_map_get_pid(globals2, i) == WS_PartitionID(PID_INVALID) || 
            usbtd_map_get_pid(globals2, i) in pids_parse_g_wimp_pids(globals2))
    {
        var old_pid_i := usbtd_map_get_pid(globals1, i);
        var new_pid_i := usbtd_map_get_pid(globals2, i);
        var cur_pid_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset;

        assert usbtd_slot_valid_pid(globals1, i);
        Lemma_usbtd_get_td_pid_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset);
        if(cur_pid_vaddr != pid_vaddr)
        {
            assert old_pid_i == new_pid_i;
        }
        else
        {
            assert new_pid_i.v == new_pid;
        }
    }

    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset, new_pid);
    Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset, new_pid);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset, new_pid);
    Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset, new_pid);
    Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset, new_pid);

    Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(globals1, globals2);

    // Prove forall i :: usbtd_map_valid_slot_id(i) ==> usbtd_map_get_idword(globals1, i) <= usbtd_id_counter_read(globals1);
    assert WK_USBTD_Map_ValidGlobalVarValues(globals1);
    Lemma_WK_USBTD_Map_ValidGlobalVarValues_P1_Equivilant(globals1);

    // Prove pre-conditions for Lemma_ValidState_ImpliesWK_ValidGlobalVarValues_ActiveUSBTDs
    forall i | usbtd_map_valid_slot_id(i)
        ensures usbtd_map_get_idword(globals2, i) <= usbtd_id_counter_read(globals2) ||
                usbtd_map_get_idword(globals2, i) == USBTD_ID_INVALID
    {
        assert usbtd_id_counter_read(globals1) == usbtd_id_counter_read(globals2);
        assert usbtd_map_get_idword(globals1, i) == usbtd_map_get_idword(globals2, i);
    }

    Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_PID_BytesOffset, new_pid);
    reveal p_usbtd_equal();
    forall i | usbtd_map_valid_slot_id(i) &&
            usbtd_map_get_pid(globals2, i) != WS_PartitionID(PID_INVALID)
        ensures usbtd_map_get_idword(globals2, i) != USBTD_ID_INVALID
    {
        if(i != slot)
        {
            assert usbtd_map_get_idword(globals1, i) == usbtd_map_get_idword(globals2, i);
            assert usbtd_map_get_pid(globals1, i) == usbtd_map_get_pid(globals2, i);
            assert usbtd_map_get_idword(globals2, i) != USBTD_ID_INVALID;
        }
        else
        {
            assert usbtd_map_get_pid(globals2, i) == WS_PartitionID(new_pid);
            assert usbtd_map_get_idword(globals2, i) != USBTD_ID_INVALID;
        }
    }

    Lemma_ValidState_ImpliesWK_ValidGlobalVarValues_ActiveUSBTDs(s'.subjects, s'.objects, s'.id_mappings, globals2);
    reveal WK_ValidGlobalVarValues_ActiveUSBTDs();
}