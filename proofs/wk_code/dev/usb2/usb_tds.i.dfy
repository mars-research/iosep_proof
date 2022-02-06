include "usb_tds.s.dfy"
include "../../partition_id.i.dfy"
include "eehci_info.i.dfy"
include "usb.i.dfy"
include "usb_tds_nlarith.i.dfy"

// Lemma: If global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM()), then
// p_usbtd_equal(globals1, globals2, i) for each i
lemma Lemma_SameUSBTDMem_Property(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM())

    ensures forall i:uint32 :: usbtd_map_valid_slot_id(i)
                ==> p_usbtd_equal(globals1, globals2, i)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();
}

lemma Lemma_WK_USBTD_Map_ValidGlobalVarValues_P1_Equivilant(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
    requires (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_id(globals, i))
        // Requirement: Property in <WK_USBTD_Map_ValidGlobalVarValues>

    ensures forall i :: usbtd_map_valid_slot_id(i)
            ==> (usbtd_map_get_idword(globals, i) <= usbtd_id_counter_read(globals) || 
                usbtd_map_get_idword(globals, i) == USBTD_ID_INVALID)
{
    forall slot:uint32 | usbtd_map_valid_slot_id(slot)
        ensures usbtd_map_get_idword(globals, slot) <= usbtd_id_counter_read(globals) || 
                usbtd_map_get_idword(globals, slot) == USBTD_ID_INVALID
    {
        assert 0 <= slot < USB_TD_ENTRY_NUM;
        assert (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_id(globals, i));
        assert usbtd_slot_valid_id(globals, slot);
    }
}

// Lemma: When replacing partition ID in <g_existing_pids>, if the old partition has no USB TD, and 
// WK_USBTD_Map_ValidGlobalVarValues(globals1), Then WK_USBTD_Map_ValidGlobalVarValues(globals2)
lemma Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfOverwritePIDOfPartitionHavingNoUSBTD(globals1:globalsmap, globals2:globalsmap, pid_vaddr:vaddr, old_pid:word, new_pid:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires pids_g_existing_pids_no_duplicate(globals1)

    requires is_valid_vaddr(pid_vaddr)
    requires is_gvar_valid_vaddr(G_Existing_PIDs(), pid_vaddr)
    requires !pids_is_os_pid(new_pid)
        // Requirement: <new_pid> must not be the OS partition's PID
    requires forall pid:WS_PartitionID :: pid in pids_parse_g_wimp_pids(globals1)
            ==> (pid.v != new_pid)
        // Requirement: <new_pid> is new
    requires forall i:int :: (0 <= i < USB_TD_ENTRY_NUM)
            ==> (usbtd_map_get_pid(globals1, i) == WS_PartitionID(PID_INVALID) ||
                usbtd_map_get_pid(globals1, i) != WS_PartitionID(old_pid));
        // Requirement: The partition of the overwritten PID must do not contain any USB TD

    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires globals2 == global_write_word(globals1, G_Existing_PIDs(), pid_vaddr, new_pid)
    requires old_pid == global_read_word(globals1, G_Existing_PIDs(), pid_vaddr)
    
    ensures WK_USBTD_Map_ValidGlobalVarValues(globals2)
{
    assert forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_pid(globals1, i) == usbtd_map_get_pid(globals2, i);

    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_pid(globals2, i) == WS_PartitionID(PID_INVALID) ||
                usbtd_map_get_pid(globals2, i) in pids_parse_g_wimp_pids(globals2)
    {
        assert usbtd_slot_valid_pid(globals1, i);
        var old_pid_i := usbtd_map_get_pid(globals1, i);
        var new_pid_i := usbtd_map_get_pid(globals2, i);

        assert old_pid_i == new_pid_i;

        if(new_pid_i != WS_PartitionID(PID_INVALID))
        {
            Lemma_pids_parse_g_wimp_pids_CorrectnessOfSetChange(globals1, globals2, pid_vaddr, old_pid, new_pid);
            assert pids_parse_g_wimp_pids(globals2) == pids_parse_g_wimp_pids(globals1) - {WS_PartitionID(old_pid)} + {WS_PartitionID(new_pid)} ||
                   pids_parse_g_wimp_pids(globals2) == pids_parse_g_wimp_pids(globals1) - {WS_PartitionID(old_pid)};

            assert old_pid_i in pids_parse_g_wimp_pids(globals1);
            assert old_pid_i in pids_parse_g_wimp_pids(globals2);
        }
    }

    Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(globals1, globals2);
}

// Lemma: If <g_existing_pids> and <g_usbtd_map_mem> is unchanged, and G_USBTD_ID_Counter is increased, and 
// WK_USBTD_Map_ValidGlobalVarValues(globals1), Then WK_USBTD_Map_ValidGlobalVarValues(globals2)
lemma Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGUSBTDIDCounterIncreased(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs())
    requires global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM())
    requires usbtd_id_counter_read(globals1) < usbtd_id_counter_read(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)

    ensures WK_USBTD_Map_ValidGlobalVarValues(globals2)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM 
        ensures usbtd_slot_valid_id(globals2, i)
    {
        assert usbtd_map_get_idword(globals1, i) == usbtd_map_get_idword(globals2, i);
        assert usbtd_slot_valid_id(globals1, i);
    }

    Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(globals1, globals2);
}

// Lemma: If <g_existing_pids> and <g_usbtd_map_mem> is unchanged, and WK_USBTD_Map_ValidGlobalVarValues(globals1),
// Then WK_USBTD_Map_ValidGlobalVarValues(globals2)
lemma Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfGExistingPIDsAndUSBTDMapMemUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs())
    requires global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM())
    requires global_read_fullval(globals1, G_USBTD_ID_Counter()) == global_read_fullval(globals2, G_USBTD_ID_Counter())
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)

    ensures WK_USBTD_Map_ValidGlobalVarValues(globals2)
{
    Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(globals1, globals2);
}

// Lemma: When updating <type> field in a USB TD, if the new type is valid, 
// and WK_USBTD_Map_ValidGlobalVarValues(globals1), Then WK_USBTD_Map_ValidGlobalVarValues(globals2)
lemma Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfNewTypeOfSlotIsValid(
    globals1:globalsmap, globals2:globalsmap, slot:uint32, type_vaddr:vaddr, new_type:word
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires type_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset

    requires is_valid_vaddr(type_vaddr)
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), type_vaddr)
    requires (new_type == USBTDs_TYPE_QTD32) || (new_type == USBTDs_TYPE_QH32) || 
            (new_type == USBTDs_TYPE_iTD32) || (new_type == USBTDs_TYPE_siTD32)
        // Requirement: The new type must be valid

    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), type_vaddr, new_type)

    ensures WK_USBTD_Map_ValidGlobalVarValues(globals2)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_type(globals2, i)
    {
        var old_type_i := usbtd_map_get_type(globals1, i);
        var new_type_i := usbtd_map_get_type(globals2, i);
        var cur_type_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset;

        assert usbtd_slot_valid_type(globals1, i);
        Lemma_usbtd_get_td_type_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset);
        if(cur_type_vaddr != type_vaddr)
        {
            assert old_type_i == new_type_i;
        }
        else
        {
            assert new_type_i == new_type;
        }
    }

    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, new_type);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, new_type);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, new_type);
    Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, new_type);
    Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, new_type);

    Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(globals1, globals2);
}

// Lemma: If new bus id is valid, and WK_USBTD_Map_ValidGlobalVarValues(globals1),
// Then WK_USBTD_Map_ValidGlobalVarValues(globals2)
lemma Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfNewBusIDIsValid(globals1:globalsmap, globals2:globalsmap, slot:uint32, busid_vaddr:vaddr, new_busid:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires busid_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset

    requires is_valid_vaddr(busid_vaddr)
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), busid_vaddr)
    requires isUInt16(new_busid)
        // Requirement: The new bus ID must be valid

    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), busid_vaddr, new_busid)

    ensures WK_USBTD_Map_ValidGlobalVarValues(globals2)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_busid(globals2, i)
    {
        var old_busid_i := usbtd_map_get_busid_word(globals1, i);
        var new_busid_i := usbtd_map_get_busid_word(globals2, i);
        var cur_busid_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset;

        assert usbtd_slot_valid_type(globals1, i);
        Lemma_usbtd_get_bus_id_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset);
        if(cur_busid_vaddr != busid_vaddr)
        {
            assert old_busid_i == new_busid_i;
            assert usbtd_slot_valid_busid(globals1, i);
            assert usbtd_slot_valid_busid(globals2, i);
        }
        else
        {
            assert new_busid_i == new_busid;
            assert usbtd_slot_valid_busid(globals2, i);
        }
    }

    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, new_busid);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, new_busid);
    Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, new_busid);
    Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, new_busid);
    Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, new_busid);

    Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(globals1, globals2);
}

// Lemma: When updating <wimpdrv_slot_id> field in a USB TD, if the new value is valid, 
// and WK_USBTD_Map_ValidGlobalVarValues(globals1), Then WK_USBTD_Map_ValidGlobalVarValues(globals2)
lemma Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfNewWimpDrvSlotIDOfSlotIsValid(
    globals1:globalsmap, globals2:globalsmap, slot:uint32, new_wimpdrv_slotid_vaddr:vaddr, new_wimpdrv_slotid:word
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires new_wimpdrv_slotid_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset

    requires is_valid_vaddr(new_wimpdrv_slotid_vaddr)
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), new_wimpdrv_slotid_vaddr)
    requires new_wimpdrv_slotid == WimpDrv_SlotID_EMPTY || wimpdrv_valid_slot_id(new_wimpdrv_slotid)
        // Requirement: The new wimpdrv_slot_id must be allowed

    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), new_wimpdrv_slotid_vaddr, new_wimpdrv_slotid)

    ensures WK_USBTD_Map_ValidGlobalVarValues(globals2)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_wimpdrv_slotid(globals2, i)
    {
        var old_new_wimpdrv_slotid_i := usbtd_map_get_wimpdrv_slotid(globals1, i);
        var new_wimpdrv_slotid_i := usbtd_map_get_wimpdrv_slotid(globals2, i);
        var cur_new_wimpdrv_slotid_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;


        assert usbtd_slot_valid_wimpdrv_slotid(globals1, i);
        Lemma_usbtd_get_wimpdrv_slotid_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset);
        if(cur_new_wimpdrv_slotid_vaddr != new_wimpdrv_slotid_vaddr)
        {
            assert old_new_wimpdrv_slotid_i == new_wimpdrv_slotid_i;
        }
        else
        {
            assert new_wimpdrv_slotid_i == new_wimpdrv_slotid;
        }
    }

    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, new_wimpdrv_slotid);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, new_wimpdrv_slotid);
    Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, new_wimpdrv_slotid);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, new_wimpdrv_slotid);
    Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, new_wimpdrv_slotid);

    Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(globals1, globals2);
}

// Lemma: When updating <usbpdev_slot_id> field in a USB TD, if the new value is valid, 
// and WK_USBTD_Map_ValidGlobalVarValues(globals1), Then WK_USBTD_Map_ValidGlobalVarValues(globals2)
lemma Lemma_WK_USB_TD_Map_ValidGlobalVarValues_HoldIfNewUSBPDevSlotIDOfSlotIsAllowed(
    globals1:globalsmap, globals2:globalsmap, slot:uint32, new_v_vaddr:vaddr, new_v:word
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires new_v_vaddr == AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset

    requires is_valid_vaddr(new_v_vaddr)
    requires is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), new_v_vaddr)
    requires new_v == WimpUSBPDev_SlotID_EMPTY || usbpdev_valid_slot_id(new_v)
        // Requirement: The new usbpdev_slot_id must be valid

    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), new_v_vaddr, new_v)

    ensures WK_USBTD_Map_ValidGlobalVarValues(globals2)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_usbpdev_slotid(globals2, i)
    {
        var old_slot_id := usbtd_map_get_usbpdev_slotid(globals1, i);
        var new_slot_id := usbtd_map_get_usbpdev_slotid(globals2, i);
        var cur_vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;


        assert usbtd_slot_valid_usbpdev_slotid(globals1, i);
        Lemma_usbtd_get_usbpdev_slotid_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset);
        if(cur_vaddr != new_v_vaddr)
        {
            assert old_slot_id == new_slot_id;
        }
        else
        {
            assert new_slot_id == new_v;
        }
    }

    Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, new_v);
    Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(globals1, globals2, slot, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, new_v);

    Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(globals1, globals2);
}

lemma Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfPIDTypeBusIDWimpDrvSlotIDUSBPDevSlotID_FieldsAreUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs())
        // Requirement: <g_existing_pids> is unchanged
    requires global_read_fullval(globals1, G_USBTD_ID_Counter()) == global_read_fullval(globals2, G_USBTD_ID_Counter())
        // Requirement: <g_usbtd_id_counter> is unchanged
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_idword(globals1, i) == usbtd_map_get_idword(globals2, i)
        // Requirement: PID field is unchanged
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_pid(globals1, i) == usbtd_map_get_pid(globals2, i)
        // Requirement: PID field is unchanged
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_type(globals1, i) == usbtd_map_get_type(globals2, i)
        // Requirement: Type field is unchanged
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_busid_word(globals1, i) == usbtd_map_get_busid_word(globals2, i)
        // Requirement: Bus ID field is unchanged
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_wimpdrv_slotid(globals1, i) == usbtd_map_get_wimpdrv_slotid(globals2, i)
        // Requirement: WimpDrv Slot ID field is unchanged
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_usbpdev_slotid(globals1, i) == usbtd_map_get_usbpdev_slotid(globals2, i)
        // Requirement: USBPDev Slot ID field is unchanged

    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)

    ensures WK_USBTD_Map_ValidGlobalVarValues(globals2)
{
    Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidIDWords_HoldIfIDsAndPIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(globals1, globals2);
    Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(globals1, globals2);
}




/*********************** For usb_tds_ops_impl.vad ********************/
// Predicate: the TD configurations in two global variables are same
predicate {:opaque} p_usbtd_content_equal(old_globals:globalsmap, new_globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbtd_map_valid_slot_id(slot)
{
    var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_WK_USB_TD_Map_PropertiesOfTDAddrs(slot);

    Lemma_usbtd_slot_offset_in_content_AlwaysValidGUSBTDMapMemAddr(slot);
    
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES) &&

    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES) &&

    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES) &&

    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES) &&

    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES) &&
    global_read_word(old_globals, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES) == global_read_word(new_globals, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES)
}

// Predicate: the USB TD in two global variables are same
predicate {:opaque} p_usbtd_equal(globals1:globalsmap, globals2:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
{
    usbtd_map_get_tdaddr(globals1, slot) == usbtd_map_get_tdaddr(globals2, slot) &&
    usbtd_map_get_idword(globals1, slot) == usbtd_map_get_idword(globals2, slot) &&
    usbtd_map_get_pid(globals1, slot) == usbtd_map_get_pid(globals2, slot) &&
    usbtd_map_get_type(globals1, slot) == usbtd_map_get_type(globals2, slot) &&
    usbtd_map_get_busid_word(globals1, slot) == usbtd_map_get_busid_word(globals2, slot) &&
    usbtd_map_get_wimpdrv_slotid(globals1, slot) == usbtd_map_get_wimpdrv_slotid(globals2, slot) &&
    usbtd_map_get_usbpdev_slotid(globals1, slot) == usbtd_map_get_usbpdev_slotid(globals2, slot) &&
    usbtd_map_get_flags(globals1, slot) == usbtd_map_get_flags(globals2, slot) &&
    usbtd_map_get_handle(globals1, slot) == usbtd_map_get_handle(globals2, slot) &&

    usbtd_map_get_inputparam(globals1, slot, G_USBTDs_MAP_ENTRY_InputParam1) == usbtd_map_get_inputparam(globals2, slot, G_USBTDs_MAP_ENTRY_InputParam1) &&
    usbtd_map_get_inputparam(globals1, slot, G_USBTDs_MAP_ENTRY_InputParam2) == usbtd_map_get_inputparam(globals2, slot, G_USBTDs_MAP_ENTRY_InputParam2) &&
    usbtd_map_get_inputparam(globals1, slot, G_USBTDs_MAP_ENTRY_InputParam3) == usbtd_map_get_inputparam(globals2, slot, G_USBTDs_MAP_ENTRY_InputParam3) &&

    p_usbtd_content_equal(globals1, globals2, slot)
}

// Predicate: Partial correctness properties of the modifying USB TD for the new global variable output by <_usbtd_slot_submit>
predicate p_usbtd_slot_submit_modification_to_usbtd(new_globals:globalsmap, td_slot:uint32,
    wimpdrv_slot_id:word, usbpdev_slot:word, input_param1:uint32, input_param2:uint32, input_param3:uint32, td_type:word, eehci_id:word
)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbtd_map_valid_slot_id(td_slot)
{
    var bus_id:word := usb_parse_eehci_id(eehci_id).bus_id;

    usbtd_slot_valid_busid(new_globals, td_slot) &&
    usbtd_map_get_busid(new_globals, td_slot) == bus_id &&
    usbtd_map_get_type(new_globals, td_slot) == td_type &&
    usbtd_map_get_wimpdrv_slotid(new_globals, td_slot) == wimpdrv_slot_id &&
    usbtd_map_get_usbpdev_slotid(new_globals, td_slot) == usbpdev_slot &&
    usbtd_map_get_inputparam(new_globals, td_slot, G_USBTDs_MAP_ENTRY_InputParam1) == input_param1 &&
    usbtd_map_get_inputparam(new_globals, td_slot, G_USBTDs_MAP_ENTRY_InputParam2) == input_param2 &&
    usbtd_map_get_inputparam(new_globals, td_slot, G_USBTDs_MAP_ENTRY_InputParam3) == input_param3 &&

    // 2. For the given td_slot, Flag has USBTD_SLOT_FLAG_SubmitDone_Bit set
    usbtd_map_get_flags(new_globals, td_slot) == SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit)
}

// Predicate: Partial correctness properties for the new global variable output by <usbtd_slot_submit_qtd32>
predicate p_usbtd_slot_submit_usbtd_ret_global(globals1:globalsmap, globals2:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(td_slot)
{
    // 1. Only the given USB TD (<td_slot>) is modified
    usbtd_map_modify_one_usbtd_only(globals1, globals2, td_slot) &&

    // 2. For the given td_slot, PID is unmodified
    usbtd_map_get_pid(globals1, td_slot) == usbtd_map_get_pid(globals2, td_slot) &&

    // 3. For the given td_slot, ID is unmodified
    usbtd_map_get_idword(globals1, td_slot) == usbtd_map_get_idword(globals2, td_slot) &&

    // 4. For the given td_slot, Flag has USBTD_SLOT_FLAG_SubmitDone_Bit set
    usbtd_map_get_flags(globals2, td_slot) == SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit)
}

// Predicate: Partial correctness properties for the new global variable output by <_usbtd_slot_submit_and_verify_qtd32_inner>
predicate p_usbtd_slot_submit_and_verify_usbtd_ret_global(globals1:globalsmap, globals2:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(td_slot)
{
    // 1. Only the given USB TD (<td_slot>) is modified
    usbtd_map_modify_one_usbtd_and_temp_usbtd_only(globals1, globals2, td_slot) &&

    // 2. For the given td_slot, PID is unmodified
    usbtd_map_get_pid(globals1, td_slot) == usbtd_map_get_pid(globals2, td_slot) &&

    // 3. For the given td_slot, ID is unmodified
    usbtd_map_get_idword(globals1, td_slot) == usbtd_map_get_idword(globals2, td_slot) &&

    // 3. For the given td_slot, Flag has USBTD_SLOT_FLAG_SubmitDone_Bit set
    usbtd_map_get_flags(globals2, td_slot) == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
}

// Predicate: Between the two global variables, only the given USB TD (<td_slot>) is modified
predicate usbtd_map_modify_one_usbtd_only(old_globals:globalsmap, new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires usbtd_map_valid_slot_id(td_slot);
{
    lemma_DistinctGlobals();

    // In <g_usbtd_map_mem>, other USB TDs are unmodified 
    (forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != td_slot
        ==> p_usbtd_equal(old_globals, new_globals, i)
    ) &&

    // Other global variables are unchanged
    globals_other_gvar_unchanged(old_globals, new_globals, G_USBTD_MAP_MEM())
}

// Predicate: Between the two global variables, only the given USB TD (<td_slot>) is modified
predicate usbtd_map_modify_one_usbtd_and_temp_usbtd_only(old_globals:globalsmap, new_globals:globalsmap, td_slot:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires usbtd_map_valid_slot_id(td_slot);
{
    lemma_DistinctGlobals();

    // In <g_usbtd_map_mem>, other USB TDs are unmodified 
    (forall i:uint32 :: usbtd_map_valid_slot_id(i) && i != td_slot
        ==> p_usbtd_equal(old_globals, new_globals, i)
    ) &&

    // Other global variables are unchanged
    globals_other_gvar_unchanged_2vars(old_globals, new_globals, G_USBTD_MAP_MEM(), G_Temp_USBTD())
}

lemma Lemma_usbtd_slot_offset_in_content_AlwaysValidGUSBTDMapMemAddr(slot:uint32)
    requires usbtd_map_valid_slot_id(slot)

    ensures var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
            forall i:int :: 0 <= i < MAX_USB_TD_BYTES/UINT32_BYTES
                ==> is_gvar_valid_addr(G_USBTD_MAP_MEM(), td_addr + i * UINT32_BYTES) &&
                    is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), td_addr + i * UINT32_BYTES)
{
    var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    forall i:int | 0 <= i < MAX_USB_TD_BYTES/UINT32_BYTES
        ensures is_gvar_valid_addr(G_USBTD_MAP_MEM(), td_addr + i * UINT32_BYTES)
    {
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(slot, G_USBTDs_MAP_ENTRY_TD_BytesOffset + i * UINT32_BYTES);
    }
}

lemma Lemma_p_usbtd_equal_transitive(globals1:globalsmap, globals2:globalsmap, globals3:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(globals3)

    requires usbtd_map_valid_slot_id(slot)

    ensures  p_usbtd_equal(globals1, globals2, slot) && p_usbtd_equal(globals2, globals3, slot)
                ==> p_usbtd_equal(globals1, globals3, slot)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();
}

lemma Lemma_p_usbtd_content_equal_transitive(globals1:globalsmap, globals2:globalsmap, globals3:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(globals3)

    requires usbtd_map_valid_slot_id(slot)

    ensures  p_usbtd_content_equal(globals1, globals2, slot) && p_usbtd_content_equal(globals2, globals3, slot)
                ==> p_usbtd_content_equal(globals1, globals3, slot)
{
    reveal p_usbtd_content_equal();
}

lemma Lemma_usbtd_id_generate_ProveIDUniqueness(globals:globalsmap, new_id:word)
    requires WK_ValidGlobalVars_Decls(globals) 
    requires forall i :: usbtd_map_valid_slot_id(i)
                ==> (usbtd_map_get_idword(globals, i) < new_id || 
                    usbtd_map_get_idword(globals, i) == USBTD_ID_INVALID)

    ensures forall i :: usbtd_map_valid_slot_id(i) &&
                usbtd_map_get_idword(globals, i) != USBTD_ID_INVALID
            ==> usbtd_map_get_idword(globals, i) != new_id
{
    // Dafny can automatically prove this lemma
}




/*********************** Utility Lemmas ********************/
// Lemma: Given a word index in G_USBTD_MAP_MEM, it always corresponds to a closest slot index and exact offset_bytes
// defined for G_USBTDs_MAP_ENTRY
lemma Lemma_USBTD_Mem_AnyWordOffsetCanBeConvertedToSlotAndBytesOffset(i:uint32) returns (slot:uint32, offset_bytes:uint32)
    requires ValidGlobalOffset(G_USBTD_MAP_MEM(), i * ARCH_WORD_BYTES)

    ensures usbtd_map_valid_slot_id(slot)
    ensures (0 <= offset_bytes < G_USBTDs_MAP_ENTRY_PID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_PID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_TYPE_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_BUSID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset)
        // Property 2
    ensures slot * G_USBTDs_MAP_ENTRY_SZ + offset_bytes == i * ARCH_WORD_BYTES
{
    var t_slot := i * ARCH_WORD_BYTES / G_USBTDs_MAP_ENTRY_SZ;
    
    // Prove usbtd_map_valid_slot_id(slot)
    lemma_DivMulLessThan(i * ARCH_WORD_BYTES, G_USBTDs_MAP_ENTRY_SZ);
    assert t_slot * G_USBTDs_MAP_ENTRY_SZ <= i * ARCH_WORD_BYTES;

    if(t_slot >= USB_TD_ENTRY_NUM)
    {
        Lemma_NatMul_Ineq_4var(USB_TD_ENTRY_NUM, G_USBTDs_MAP_ENTRY_SZ, t_slot, G_USBTDs_MAP_ENTRY_SZ);
        assert t_slot * G_USBTDs_MAP_ENTRY_SZ >= USB_TD_ENTRY_NUM * G_USBTDs_MAP_ENTRY_SZ;

        assert false;
    }
    assert t_slot < USB_TD_ENTRY_NUM;

    lemma_DivBounds(i * ARCH_WORD_BYTES, G_USBTDs_MAP_ENTRY_SZ);
    assert t_slot >= 0;

    slot := t_slot;

    // Prove isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ)
    lemma_MulSign(slot, G_USBTDs_MAP_ENTRY_SZ);
    assert slot * G_USBTDs_MAP_ENTRY_SZ >= 0;
    assert slot * G_USBTDs_MAP_ENTRY_SZ <= i * ARCH_WORD_BYTES;
    assert isUInt32(slot * G_USBTDs_MAP_ENTRY_SZ);

    // Prove isUInt32(t_offset_bytes);
    var t_offset_bytes := i * ARCH_WORD_BYTES - slot * G_USBTDs_MAP_ENTRY_SZ;
    assert isUInt32(i * ARCH_WORD_BYTES);
    assert isUInt32(t_offset_bytes);

    offset_bytes := t_offset_bytes;

    // Prove offset fulfill property 2
    assert slot * G_USBTDs_MAP_ENTRY_SZ + offset_bytes == i * ARCH_WORD_BYTES;

    //assert offset_bytes < G_USBTDs_MAP_ENTRY_SZ;
    //assert offset_bytes != G_USBTDs_MAP_ENTRY_TYPE_BytesOffset + 1;

    // [TODO-Important]
    assume (0 <= offset_bytes < G_USBTDs_MAP_ENTRY_PID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_PID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_TYPE_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_BUSID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);
}

// Lemma: If each USB TD slot is equal in two global variables, then the entire G_USBTD_MAP_MEM must be the same
lemma Lemma_USBTD_Map_MEM_IfAllUSBTDSlotsEqual_ThenEntireMemEqual(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires forall i:uint32 :: usbtd_map_valid_slot_id(i)
                ==> p_usbtd_equal(globals1, globals2, i)

    ensures global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM())
{
    reveal p_usbtd_content_equal();
    reveal p_usbtd_equal();

    lemma_DistinctGlobals();
    
    var seq1 := global_read_fullval(globals1, G_USBTD_MAP_MEM());
    var seq2 :=  global_read_fullval(globals2, G_USBTD_MAP_MEM());
    assert |seq1| == |seq2|;

    if(seq1 != seq2)
    {
        var i :| 0 <= i < |seq1| && seq1[i] != seq2[i];

        var slot, offset_bytes := Lemma_USBTD_Mem_AnyWordOffsetCanBeConvertedToSlotAndBytesOffset(i);
        assert (0 <= offset_bytes < G_USBTDs_MAP_ENTRY_PID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_PID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_TYPE_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_BUSID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset) ||
               (offset_bytes == G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);

        assert false;
    }
}

// Lemma: If each word of USB TD is the same, then <p_usbtd_content_equal> holds
lemma Lemma_usbtd_equal_ProveEquivilant(globals1:globalsmap, globals2:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    

    requires p_usbtd_content_equal(globals1, globals2, slot)
    requires usbtd_map_get_idword(globals1, slot) == usbtd_map_get_idword(globals2, slot)
    requires usbtd_map_get_pid(globals1, slot) == usbtd_map_get_pid(globals2, slot)
    requires usbtd_map_get_type(globals1, slot) == usbtd_map_get_type(globals2, slot)
    requires usbtd_map_get_busid_word(globals1, slot) == usbtd_map_get_busid_word(globals2, slot)
    requires usbtd_map_get_flags(globals1, slot) == usbtd_map_get_flags(globals2, slot)
    requires usbtd_map_get_wimpdrv_slotid(globals1, slot) == usbtd_map_get_wimpdrv_slotid(globals2, slot)
    requires usbtd_map_get_usbpdev_slotid(globals1, slot) == usbtd_map_get_usbpdev_slotid(globals2, slot)
    requires usbtd_map_get_handle(globals1, slot) == usbtd_map_get_handle(globals2, slot)
    requires usbtd_map_get_inputparam(globals1, slot, G_USBTDs_MAP_ENTRY_InputParam1) == usbtd_map_get_inputparam(globals2, slot, G_USBTDs_MAP_ENTRY_InputParam1)
    requires usbtd_map_get_inputparam(globals1, slot, G_USBTDs_MAP_ENTRY_InputParam2) == usbtd_map_get_inputparam(globals2, slot, G_USBTDs_MAP_ENTRY_InputParam2)
    requires usbtd_map_get_inputparam(globals1, slot, G_USBTDs_MAP_ENTRY_InputParam3) == usbtd_map_get_inputparam(globals2, slot, G_USBTDs_MAP_ENTRY_InputParam3)

    ensures p_usbtd_equal(globals1, globals2, slot)
{
    reveal p_usbtd_equal();
}

// Lemma: If each word of USB TD content is the same, then <p_usbtd_content_equal> holds
lemma Lemma_usbtd_content_equal_ProveEquivilant(globals1:globalsmap, globals2:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
            forall j :: 0 <= j < MAX_USB_TD_BYTES/UINT32_BYTES
                ==> is_gvar_valid_addr(G_USBTD_MAP_MEM(), td_addr + j * UINT32_BYTES) &&
                    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + j * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + j * UINT32_BYTES)

    ensures p_usbtd_content_equal(globals1, globals2, slot)
{
    reveal p_usbtd_content_equal();


    var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
    Lemma_WK_USB_TD_Map_PropertiesOfTDAddrs(slot);
    Lemma_usbtd_slot_offset_in_content_AlwaysValidGUSBTDMapMemAddr(slot);

    assert global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 0 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 0 * UINT32_BYTES);
    assert global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr);
    assert global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 1 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 2 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 3 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 4 * UINT32_BYTES) &&

    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 5 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 6 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 7 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 8 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 9 * UINT32_BYTES) &&

    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 10 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 11 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 12 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 13 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 14 * UINT32_BYTES) &&

    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 15 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 16 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 17 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 18 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 19 * UINT32_BYTES) &&

    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 20 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 21 * UINT32_BYTES) &&
    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + 22 * UINT32_BYTES);
}

lemma Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot_USBTDContents(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: usbtd_map_valid_slot_id(i) && i != slot
                ==> p_usbtd_content_equal(globals1, globals2, i)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    forall i:uint32 | usbtd_map_valid_slot_id(i) && i != slot
        ensures p_usbtd_content_equal(globals1, globals2, i)
    {
        forall j | 0 <= j < MAX_USB_TD_BYTES/UINT32_BYTES
            ensures var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
                    is_gvar_valid_addr(G_USBTD_MAP_MEM(), td_addr + j * UINT32_BYTES) &&
                    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + j * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + j * UINT32_BYTES)
        {
            var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
            var offset_in_td := j * UINT32_BYTES;
            
            Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + offset_in_td);
            assert is_gvar_valid_vaddr(G_USBTD_MAP_MEM(), td_addr + offset_in_td);
            if(global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + offset_in_td) != global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + offset_in_td))
            {
                assert i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset + offset_in_td == slot * G_USBTDs_MAP_ENTRY_SZ + offset;
                Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + offset_in_td, slot, offset);
                assert false;
            }
            assert global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + offset_in_td) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + offset_in_td);
        }

        Lemma_usbtd_content_equal_ProveEquivilant(globals1, globals2, i);
    }
}

// Lemma: Other USB TD slots are unmodified when modifying the USB TD at <slot>
lemma Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: usbtd_map_valid_slot_id(i) && i != slot
                ==> p_usbtd_equal(globals1, globals2, i)
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    forall i:uint32 | usbtd_map_valid_slot_id(i) && i != slot
        ensures p_usbtd_equal(globals1, globals2, i)
    {
        assert usbtd_map_get_tdaddr(globals1, i) == usbtd_map_get_tdaddr(globals2, i);

        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_ID_BytesOffset);        
        if(usbtd_map_get_idword(globals1, i) != usbtd_map_get_idword(globals2, i))
        {
            var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset;
            assert global_read_word(globals1, G_USBTD_MAP_MEM(), vaddr1) != global_read_word(globals2, G_USBTD_MAP_MEM(), vaddr1);
            assert i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset == slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_USBTDs_MAP_ENTRY_ID_BytesOffset, slot, offset);
            assert false;
        }
        assert usbtd_map_get_idword(globals1, i) == usbtd_map_get_idword(globals2, i);

        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_PID_BytesOffset);        
        if(usbtd_map_get_pid(globals1, i) != usbtd_map_get_pid(globals2, i))
        {
            var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset;
            assert global_read_word(globals1, G_USBTD_MAP_MEM(), vaddr1) != global_read_word(globals2, G_USBTD_MAP_MEM(), vaddr1);
            assert i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset == slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_USBTDs_MAP_ENTRY_PID_BytesOffset, slot, offset);
            assert false;
        }
        assert usbtd_map_get_pid(globals1, i) == usbtd_map_get_pid(globals2, i);

        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset);
        if(usbtd_map_get_type(globals1, i) != usbtd_map_get_type(globals2, i))
        {
            var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset;
            assert global_read_word(globals1, G_USBTD_MAP_MEM(), vaddr1) != global_read_word(globals2, G_USBTD_MAP_MEM(), vaddr1);
            assert i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset == slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_USBTDs_MAP_ENTRY_TYPE_BytesOffset, slot, offset);
            assert false;
        }
        assert usbtd_map_get_type(globals1, i) == usbtd_map_get_type(globals2, i);

        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset);
        if(usbtd_map_get_busid_word(globals1, i) != usbtd_map_get_busid_word(globals2, i))
        {
            var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset;
            assert global_read_word(globals1, G_USBTD_MAP_MEM(), vaddr1) != global_read_word(globals2, G_USBTD_MAP_MEM(), vaddr1);
            assert i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset == slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_USBTDs_MAP_ENTRY_BUSID_BytesOffset, slot, offset);
            assert false;
        }
        assert usbtd_map_get_busid_word(globals1, i) == usbtd_map_get_busid_word(globals2, i);

        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset);
        if(usbtd_map_get_wimpdrv_slotid(globals1, i) != usbtd_map_get_wimpdrv_slotid(globals2, i))
        {
            var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;
            assert global_read_word(globals1, G_USBTD_MAP_MEM(), vaddr1) != global_read_word(globals2, G_USBTD_MAP_MEM(), vaddr1);
            assert i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset == slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset, slot, offset);
            assert false;
        }
        assert usbtd_map_get_wimpdrv_slotid(globals1, i) == usbtd_map_get_wimpdrv_slotid(globals2, i);

        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset);
        if(usbtd_map_get_usbpdev_slotid(globals1, i) != usbtd_map_get_usbpdev_slotid(globals2, i))
        {
            var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;
            assert global_read_word(globals1, G_USBTD_MAP_MEM(), vaddr1) != global_read_word(globals2, G_USBTD_MAP_MEM(), vaddr1);
            assert i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset == slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset, slot, offset);
            assert false;
        }
        assert usbtd_map_get_usbpdev_slotid(globals1, i) == usbtd_map_get_usbpdev_slotid(globals2, i);

        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset);
        if(usbtd_map_get_flags(globals1, i) != usbtd_map_get_flags(globals2, i))
        {
            var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset;
            assert global_read_word(globals1, G_USBTD_MAP_MEM(), vaddr1) != global_read_word(globals2, G_USBTD_MAP_MEM(), vaddr1);
            assert i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset == slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset, slot, offset);
            assert false;
        }
        assert usbtd_map_get_flags(globals1, i) == usbtd_map_get_flags(globals2, i);

        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset);
        if(usbtd_map_get_handle(globals1, i) != usbtd_map_get_handle(globals2, i))
        {
            var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset;
            assert global_read_word(globals1, G_USBTD_MAP_MEM(), vaddr1) != global_read_word(globals2, G_USBTD_MAP_MEM(), vaddr1);
            assert i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset == slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset, slot, offset);
            assert false;
        }
        assert usbtd_map_get_handle(globals1, i) == usbtd_map_get_handle(globals2, i);

    
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset);
        if(usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam1) != usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam1))
        {
            var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset;
            assert global_read_word(globals1, G_USBTD_MAP_MEM(), vaddr1) != global_read_word(globals2, G_USBTD_MAP_MEM(), vaddr1);
            assert i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset == slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset, slot, offset);
            assert false;
        }

        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset);
        if(usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam2) != usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam2))
        {
            var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset;
            assert global_read_word(globals1, G_USBTD_MAP_MEM(), vaddr1) != global_read_word(globals2, G_USBTD_MAP_MEM(), vaddr1);
            assert i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset == slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset, slot, offset);
            assert false;
        }

        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset);
        if(usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam3) != usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam3))
        {
            var vaddr1 := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset;
            assert global_read_word(globals1, G_USBTD_MAP_MEM(), vaddr1) != global_read_word(globals2, G_USBTD_MAP_MEM(), vaddr1);
            assert i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset == slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            Lemma_usbtd_slot_offset_UniquePairForVAddr_ForContradictionProof(i, G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset, slot, offset);
            assert false;
        }

        assert usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam1) == usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam1);
        assert usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam2) == usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam2);
        assert usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam3) == usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam3);

        Lemma_USBTD_PreserveOtherSlots_WhenModifyingOneSlot_USBTDContents(globals1, globals2, slot, offset, new_v);
        assert p_usbtd_content_equal(globals1, globals2, i);
    }
}

// Lemma: Other global variables are unmodified when modifying the USB TD at <slot>
lemma Lemma_USBTD_PreserveOtherGvars_WhenModifyingOneSlot(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures globals_other_gvar_unchanged(globals1, globals2, G_USBTD_MAP_MEM())
{
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();
}

// Lemma: If <global_non_scratchpad_vars_are_unchanged> holds, then all USB TDs are unchanged
lemma Lemma_global_non_scratchpad_vars_are_unchanged_ImpliesEqualUSBTDs(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires global_non_scratchpad_vars_are_unchanged(globals1, globals2)

    ensures forall i:uint32 :: usbtd_map_valid_slot_id(i)
        ==> p_usbtd_equal(globals1, globals2, i)
{
    reveal global_non_scratchpad_vars_are_unchanged();
    reveal p_usbtd_equal();
    reveal p_usbtd_content_equal();

    forall i:uint32 | usbtd_map_valid_slot_id(i)
        ensures p_usbtd_equal(globals1, globals2, i)
    {
        // Dafny can automatically prove this.
    }
}

// Lemma: If G_USBTD_MAP_MEM is unchanged, then usbtds_verifiedtds_do_not_associate_usb_pdev holds
lemma Lemma_usbtds_verifiedtds_do_not_associate_usb_pdev_HoldIfGUSBTDMemUnchanged(globals1:globalsmap, globals2:globalsmap, usbpdev_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbpdev_valid_slot_id(usbpdev_slot)
    requires global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM())
    requires usbtds_verifiedtds_do_not_associate_usb_pdev(globals1, usbpdev_slot)

    ensures usbtds_verifiedtds_do_not_associate_usb_pdev(globals2, usbpdev_slot)
{
    // Dafny can automatically prove this lemma
}




/*********************** Private Lemmas ********************/
// Lemma: If <id> fields of <g_usbtd_mem_map> and <g_usbtd_id_counter> are unmodified, then the new global variable 
// satisfies usbtd_slot_valid_id
lemma Lemma_WK_USB_TD_Map_USBTDSlotValidID_HoldIfIDsAreUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires global_read_fullval(globals1, G_USBTD_ID_Counter()) == global_read_fullval(globals2, G_USBTD_ID_Counter())
        // Requirement: <g_usbtd_id_counter> is unchanged
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_idword(globals1, i) == usbtd_map_get_idword(globals2, i)
        // Requirement: ID field is unchanged

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_id(globals1, i)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_id(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_id(globals2, i)
    {
        var v1 := usbtd_map_get_idword(globals1, i); 
        var v2 := usbtd_map_get_idword(globals2, i);
        assert v1 == v2;

        assert usbtd_slot_valid_id(globals1, i);
    }
}

// Lemma: If <id> fields of <g_usbtd_mem_map> and <g_usbtd_id_counter> are unmodified, then the new global variable 
// satisfies WK_USBTD_Map_ValidGlobalVarValues_IDWords
lemma Lemma_WK_USB_TD_Map_USBTDSlotValidIDWords_HoldIfIDsAndPIDsAreUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_idword(globals1, i) == usbtd_map_get_idword(globals2, i)
        // Requirement: ID field is unchanged
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_pid(globals1, i) == usbtd_map_get_pid(globals2, i)

    requires WK_USBTD_Map_ValidGlobalVarValues_IDWords(globals1)

    ensures WK_USBTD_Map_ValidGlobalVarValues_IDWords(globals2)
{
    forall i, j | usbtd_map_valid_slot_id(i) && usbtd_map_valid_slot_id(j) &&
            usbtd_map_get_idword(globals2, i) != USBTD_ID_INVALID && usbtd_map_get_idword(globals2, j) != USBTD_ID_INVALID
        ensures usbtd_map_get_idword(globals2, i) == usbtd_map_get_idword(globals2, j) <==> i == j
    {
        assert usbtd_map_get_idword(globals1, i) == usbtd_map_get_idword(globals2, i);
        assert usbtd_map_get_idword(globals1, j) == usbtd_map_get_idword(globals2, j);
    }

    forall slot | usbtd_map_valid_slot_id(slot) &&
            usbtd_map_get_pid(globals2, slot) != WS_PartitionID(PID_INVALID)
        ensures usbtd_map_get_idword(globals2, slot) != USBTD_ID_INVALID
    {
        assert usbtd_map_get_idword(globals1, slot) == usbtd_map_get_idword(globals2, slot);
    }
}

// Lemma: If <pid> fields of <g_usbtd_mem_map> and <g_existing_pids> are unmodified, then the new global variable 
// satisfies usbtd_slot_valid_pid
lemma Lemma_WK_USB_TD_Map_USBTDSlotValidPID_HoldIfPIDsAreUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs())
        // Requirement: <g_existing_pids> is unchanged
    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_pid(globals1, i) == usbtd_map_get_pid(globals2, i)
        // Requirement: PID field is unchanged

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_pid(globals1, i)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_pid(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_pid(globals2, i)
    {
        var v1 := usbtd_map_get_pid(globals1, i); 
        var v2 := usbtd_map_get_pid(globals2, i);
        assert v1 == v2;

        assert usbtd_slot_valid_pid(globals1, i);
        assert usbtd_map_get_pid(globals1, i) == WS_PartitionID(PID_INVALID) || 
                usbtd_map_get_pid(globals1, i) in pids_parse_g_wimp_pids(globals1);

        assert usbtd_map_get_pid(globals2, i) == WS_PartitionID(PID_INVALID) || 
                usbtd_map_get_pid(globals2, i) in pids_parse_g_wimp_pids(globals2);
    }
}

// Lemma: If <type> fields of <g_usbtd_mem_map> is unmodified, then the new global variable satisfies USBTDSlotValidType
lemma Lemma_WK_USB_TD_Map_USBTDSlotValidType_HoldIfTypesAreUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_type(globals1, i) == usbtd_map_get_type(globals2, i)
        // Requirement: Type field is unchanged

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_type(globals1, i)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_type(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_type(globals2, i)
    {
        var v1 := usbtd_map_get_type(globals1, i); 
        var v2 := usbtd_map_get_type(globals2, i);
        assert v1 == v2;

        assert usbtd_slot_valid_type(globals1, i);
        assert (v1 == USBTDs_TYPE_QTD32) || (v1 == USBTDs_TYPE_QH32) || 
                (v1 == USBTDs_TYPE_iTD32) || (v1 == USBTDs_TYPE_siTD32);

        assert (v2 == USBTDs_TYPE_QTD32) || (v2 == USBTDs_TYPE_QH32) || 
                (v2 == USBTDs_TYPE_iTD32) || (v2 == USBTDs_TYPE_siTD32);
    }
}

// Lemma: If <bus_id> fields of <g_usbtd_mem_map> is unmodified, then the new global variable satisfies USBTDSlotValidBUsID
lemma Lemma_WK_USB_TD_Map_USBTDSlotValidBusID_HoldIfBusIDWordsAreUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_busid_word(globals1, i) == usbtd_map_get_busid_word(globals2, i)
        // Requirement: Bus ID field is unchanged

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_busid(globals1, i)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_busid(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_busid(globals2, i)
    {
        var v1 := usbtd_map_get_busid_word(globals1, i); 
        var v2 := usbtd_map_get_busid_word(globals2, i);
        assert v1 == v2;

        assert usbtd_slot_valid_busid(globals1, i);
    }
}

// Lemma: If <wimpdrv_slot_id> fields of <g_usbtd_mem_map> is unmodified, then the new global variable satisfies 
// usbtd_slot_valid_wimpdrv_slotid
lemma Lemma_WK_USB_TD_Map_USBTDSlotValidWimpDrvSlotID_HoldIfWimpDrvSlotIDsAreUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_wimpdrv_slotid(globals1, i) == usbtd_map_get_wimpdrv_slotid(globals2, i)
        // Requirement: Type field is unchanged

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_wimpdrv_slotid(globals1, i)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_wimpdrv_slotid(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_wimpdrv_slotid(globals2, i)
    {
        var v1 := usbtd_map_get_wimpdrv_slotid(globals1, i); 
        var v2 := usbtd_map_get_wimpdrv_slotid(globals2, i);
        assert v1 == v2;

        assert usbtd_slot_valid_wimpdrv_slotid(globals1, i);
    }
}

// Lemma: If <usbpdev_slot_id> fields of <g_usbtd_mem_map> is unmodified, then the new global variable satisfies 
// usbtd_slot_valid_usbpdev_slotid
lemma Lemma_WK_USB_TD_Map_USBTDSlotValidUSBPDevSlotID_HoldIfUSBPDevSlotIDsAreUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM
        ==> usbtd_map_get_usbpdev_slotid(globals1, i) == usbtd_map_get_usbpdev_slotid(globals2, i)
        // Requirement: Type field is unchanged

    requires forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_usbpdev_slotid(globals1, i)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_usbpdev_slotid(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_slot_valid_usbpdev_slotid(globals2, i)
    {
        var v1 := usbtd_map_get_usbpdev_slotid(globals1, i); 
        var v2 := usbtd_map_get_usbpdev_slotid(globals2, i);
        assert v1 == v2;

        assert usbtd_slot_valid_usbpdev_slotid(globals1, i);
    }
}

lemma Lemma_WK_USB_TD_Map_PreservePIDFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires offset != G_USBTDs_MAP_ENTRY_PID_BytesOffset
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_pid(globals1, i) == usbtd_map_get_pid(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_pid(globals1, i) == usbtd_map_get_pid(globals2, i)
    {
        var pid_offset := i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_PID_BytesOffset;

        // Prove ValidGlobalOffset(G_USBTD_MAP_MEM(), pid_offset)
        Lemma_usbtd_get_td_pid_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, pid_offset);
        assert ValidGlobalOffset(G_USBTD_MAP_MEM(), pid_offset);

        // Prove pid_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
        if(pid_offset == slot * G_USBTDs_MAP_ENTRY_SZ + offset)
        {
            assert 0 - G_USBTDs_MAP_ENTRY_SZ < offset - G_USBTDs_MAP_ENTRY_PID_BytesOffset < G_USBTDs_MAP_ENTRY_SZ;
            assert slot != i;

            assert offset - G_USBTDs_MAP_ENTRY_PID_BytesOffset == i * G_USBTDs_MAP_ENTRY_SZ - slot * G_USBTDs_MAP_ENTRY_SZ;
            lemma_MulDistrib_Sub(i, slot, G_USBTDs_MAP_ENTRY_SZ);
            assert offset - G_USBTDs_MAP_ENTRY_PID_BytesOffset == (i - slot) * G_USBTDs_MAP_ENTRY_SZ;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_PID_BytesOffset >= G_USBTDs_MAP_ENTRY_SZ;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_PID_BytesOffset <= -1 * G_USBTDs_MAP_ENTRY_SZ;
                Lemma_IntMul_EqualityOfMinusN(G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_PID_BytesOffset <= 0 - G_USBTDs_MAP_ENTRY_SZ;
            }
            assert false;
        }
        assert pid_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
    }
}

lemma Lemma_WK_USB_TD_Map_PreserveTypeFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires offset != G_USBTDs_MAP_ENTRY_TYPE_BytesOffset
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_type(globals1, i) == usbtd_map_get_type(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_type(globals1, i) == usbtd_map_get_type(globals2, i)
    {
        var v_offset := i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TYPE_BytesOffset;

        // Prove ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset)
        Lemma_usbtd_get_td_type_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset);

        // Prove v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
        if(v_offset == slot * G_USBTDs_MAP_ENTRY_SZ + offset)
        {
            assert 0 - G_USBTDs_MAP_ENTRY_SZ < offset - G_USBTDs_MAP_ENTRY_TYPE_BytesOffset < G_USBTDs_MAP_ENTRY_SZ;
            assert slot != i;

            assert offset - G_USBTDs_MAP_ENTRY_TYPE_BytesOffset == i * G_USBTDs_MAP_ENTRY_SZ - slot * G_USBTDs_MAP_ENTRY_SZ;
            lemma_MulDistrib_Sub(i, slot, G_USBTDs_MAP_ENTRY_SZ);
            assert offset - G_USBTDs_MAP_ENTRY_TYPE_BytesOffset == (i - slot) * G_USBTDs_MAP_ENTRY_SZ;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_TYPE_BytesOffset >= G_USBTDs_MAP_ENTRY_SZ;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_TYPE_BytesOffset <= -1 * G_USBTDs_MAP_ENTRY_SZ;
                Lemma_IntMul_EqualityOfMinusN(G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_TYPE_BytesOffset <= 0 - G_USBTDs_MAP_ENTRY_SZ;
            }
            assert false;
        }
        assert v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
    }
}


lemma Lemma_WK_USB_TD_Map_PreserveBusIDFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires offset != G_USBTDs_MAP_ENTRY_BUSID_BytesOffset
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_busid_word(globals1, i) == usbtd_map_get_busid_word(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_busid_word(globals1, i) == usbtd_map_get_busid_word(globals2, i)
    {
        var v_offset := i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_BUSID_BytesOffset;

        // Prove ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset)
        Lemma_usbtd_get_bus_id_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset);

        // Prove v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
        if(v_offset == slot * G_USBTDs_MAP_ENTRY_SZ + offset)
        {
            assert 0 - G_USBTDs_MAP_ENTRY_SZ < offset - G_USBTDs_MAP_ENTRY_BUSID_BytesOffset < G_USBTDs_MAP_ENTRY_SZ;
            assert slot != i;

            assert offset - G_USBTDs_MAP_ENTRY_BUSID_BytesOffset == i * G_USBTDs_MAP_ENTRY_SZ - slot * G_USBTDs_MAP_ENTRY_SZ;
            lemma_MulDistrib_Sub(i, slot, G_USBTDs_MAP_ENTRY_SZ);
            assert offset - G_USBTDs_MAP_ENTRY_BUSID_BytesOffset == (i - slot) * G_USBTDs_MAP_ENTRY_SZ;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_BUSID_BytesOffset >= G_USBTDs_MAP_ENTRY_SZ;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_BUSID_BytesOffset <= -1 * G_USBTDs_MAP_ENTRY_SZ;
                Lemma_IntMul_EqualityOfMinusN(G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_BUSID_BytesOffset <= 0 - G_USBTDs_MAP_ENTRY_SZ;
            }
            assert false;
        }
        assert v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
    }
}

lemma Lemma_WK_USB_TD_Map_PreserveUSBPDevSlotIDFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires offset != G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_usbpdev_slotid(globals1, i) == usbtd_map_get_usbpdev_slotid(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_usbpdev_slotid(globals1, i) == usbtd_map_get_usbpdev_slotid(globals2, i)
    {
        var v_offset := i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset;

        // Prove ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset)
        Lemma_usbtd_get_usbpdev_slotid_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset);

        // Prove v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
        if(v_offset == slot * G_USBTDs_MAP_ENTRY_SZ + offset)
        {
            assert 0 - G_USBTDs_MAP_ENTRY_SZ < offset - G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset < G_USBTDs_MAP_ENTRY_SZ;
            assert slot != i;

            assert offset - G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset == i * G_USBTDs_MAP_ENTRY_SZ - slot * G_USBTDs_MAP_ENTRY_SZ;
            lemma_MulDistrib_Sub(i, slot, G_USBTDs_MAP_ENTRY_SZ);
            assert offset - G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset == (i - slot) * G_USBTDs_MAP_ENTRY_SZ;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset >= G_USBTDs_MAP_ENTRY_SZ;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset <= -1 * G_USBTDs_MAP_ENTRY_SZ;
                Lemma_IntMul_EqualityOfMinusN(G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset <= 0 - G_USBTDs_MAP_ENTRY_SZ;
            }
            assert false;
        }
        assert v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
    }
}

lemma Lemma_WK_USB_TD_Map_PreserveWimpDrvSlotIDFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires offset != G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_wimpdrv_slotid(globals1, i) == usbtd_map_get_wimpdrv_slotid(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_wimpdrv_slotid(globals1, i) == usbtd_map_get_wimpdrv_slotid(globals2, i)
    {
        var v_offset := i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset;

        // Prove ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset)
        Lemma_usbtd_get_wimpdrv_slotid_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset);

        // Prove v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
        if(v_offset == slot * G_USBTDs_MAP_ENTRY_SZ + offset)
        {
            assert 0 - G_USBTDs_MAP_ENTRY_SZ < offset - G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset < G_USBTDs_MAP_ENTRY_SZ;
            assert slot != i;

            assert offset - G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset == i * G_USBTDs_MAP_ENTRY_SZ - slot * G_USBTDs_MAP_ENTRY_SZ;
            lemma_MulDistrib_Sub(i, slot, G_USBTDs_MAP_ENTRY_SZ);
            assert offset - G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset == (i - slot) * G_USBTDs_MAP_ENTRY_SZ;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset >= G_USBTDs_MAP_ENTRY_SZ;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset <= -1 * G_USBTDs_MAP_ENTRY_SZ;
                Lemma_IntMul_EqualityOfMinusN(G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset <= 0 - G_USBTDs_MAP_ENTRY_SZ;
            }
            assert false;
        }
        assert v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
    }
}

lemma Lemma_WK_USB_TD_Map_PreserveIDFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires offset != G_USBTDs_MAP_ENTRY_ID_BytesOffset
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_idword(globals1, i) == usbtd_map_get_idword(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_idword(globals1, i) == usbtd_map_get_idword(globals2, i)
    {
        var v_offset := i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_ID_BytesOffset;

        // Prove ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset)
        Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_ID_BytesOffset);
        assert ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset);

        // Prove v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
        if(v_offset == slot * G_USBTDs_MAP_ENTRY_SZ + offset)
        {
            assert 0 - G_USBTDs_MAP_ENTRY_SZ < offset - G_USBTDs_MAP_ENTRY_ID_BytesOffset < G_USBTDs_MAP_ENTRY_SZ;
            assert slot != i;

            assert offset - G_USBTDs_MAP_ENTRY_ID_BytesOffset == i * G_USBTDs_MAP_ENTRY_SZ - slot * G_USBTDs_MAP_ENTRY_SZ;
            lemma_MulDistrib_Sub(i, slot, G_USBTDs_MAP_ENTRY_SZ);
            assert offset - G_USBTDs_MAP_ENTRY_ID_BytesOffset == (i - slot) * G_USBTDs_MAP_ENTRY_SZ;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_ID_BytesOffset >= G_USBTDs_MAP_ENTRY_SZ;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_ID_BytesOffset <= -1 * G_USBTDs_MAP_ENTRY_SZ;
                Lemma_IntMul_EqualityOfMinusN(G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_ID_BytesOffset <= 0 - G_USBTDs_MAP_ENTRY_SZ;
            }
            assert false;
        }
        assert v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
    }
}

lemma Lemma_WK_USB_TD_Map_PreserveFlagsFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires offset != G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_flags(globals1, i) == usbtd_map_get_flags(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_flags(globals1, i) == usbtd_map_get_flags(globals2, i)
    {
        var v_offset := i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset;

        // Prove ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset)
        Lemma_usbtd_get_flag_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset);

        // Prove v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
        if(v_offset == slot * G_USBTDs_MAP_ENTRY_SZ + offset)
        {
            assert 0 - G_USBTDs_MAP_ENTRY_SZ < offset - G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset < G_USBTDs_MAP_ENTRY_SZ;
            assert slot != i;

            assert offset - G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset == i * G_USBTDs_MAP_ENTRY_SZ - slot * G_USBTDs_MAP_ENTRY_SZ;
            lemma_MulDistrib_Sub(i, slot, G_USBTDs_MAP_ENTRY_SZ);
            assert offset - G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset == (i - slot) * G_USBTDs_MAP_ENTRY_SZ;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset >= G_USBTDs_MAP_ENTRY_SZ;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset <= -1 * G_USBTDs_MAP_ENTRY_SZ;
                Lemma_IntMul_EqualityOfMinusN(G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset <= 0 - G_USBTDs_MAP_ENTRY_SZ;
            }
            assert false;
        }
        assert v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
    }
}

lemma Lemma_WK_USB_TD_Map_PreserveHandleFieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires offset != G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_handle(globals1, i) == usbtd_map_get_handle(globals2, i)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_handle(globals1, i) == usbtd_map_get_handle(globals2, i)
    {
        var v_offset := i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset;

        // Prove ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset)
        Lemma_usbtd_get_handle_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset);

        // Prove v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
        if(v_offset == slot * G_USBTDs_MAP_ENTRY_SZ + offset)
        {
            assert 0 - G_USBTDs_MAP_ENTRY_SZ < offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset < G_USBTDs_MAP_ENTRY_SZ;
            assert slot != i;

            assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset == i * G_USBTDs_MAP_ENTRY_SZ - slot * G_USBTDs_MAP_ENTRY_SZ;
            lemma_MulDistrib_Sub(i, slot, G_USBTDs_MAP_ENTRY_SZ);
            assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset == (i - slot) * G_USBTDs_MAP_ENTRY_SZ;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset >= G_USBTDs_MAP_ENTRY_SZ;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset <= -1 * G_USBTDs_MAP_ENTRY_SZ;
                Lemma_IntMul_EqualityOfMinusN(G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset <= 0 - G_USBTDs_MAP_ENTRY_SZ;
            }
            assert false;
        }
        assert v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
    }
}

lemma Lemma_WK_USB_TD_Map_PreserveInputParam1FieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires offset != G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam1) == usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam1)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam1) == usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam1)
    {
        var v_offset := i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset;

        // Prove ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset)
        Lemma_usbtd_get_inputparams_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset);

        // Prove v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
        if(v_offset == slot * G_USBTDs_MAP_ENTRY_SZ + offset)
        {
            assert 0 - G_USBTDs_MAP_ENTRY_SZ < offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset < G_USBTDs_MAP_ENTRY_SZ;
            assert slot != i;

            assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset == i * G_USBTDs_MAP_ENTRY_SZ - slot * G_USBTDs_MAP_ENTRY_SZ;
            lemma_MulDistrib_Sub(i, slot, G_USBTDs_MAP_ENTRY_SZ);
            assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset == (i - slot) * G_USBTDs_MAP_ENTRY_SZ;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset >= G_USBTDs_MAP_ENTRY_SZ;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset <= -1 * G_USBTDs_MAP_ENTRY_SZ;
                Lemma_IntMul_EqualityOfMinusN(G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset <= 0 - G_USBTDs_MAP_ENTRY_SZ;
            }
            assert false;
        }
        assert v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
    }
}

lemma Lemma_WK_USB_TD_Map_PreserveInputParam2FieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires offset != G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam2) == usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam2)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam2) == usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam2)
    {
        var v_offset := i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset;

        // Prove ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset)
        Lemma_usbtd_get_inputparams_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset);

        // Prove v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
        if(v_offset == slot * G_USBTDs_MAP_ENTRY_SZ + offset)
        {
            assert 0 - G_USBTDs_MAP_ENTRY_SZ < offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset < G_USBTDs_MAP_ENTRY_SZ;
            assert slot != i;

            assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset == i * G_USBTDs_MAP_ENTRY_SZ - slot * G_USBTDs_MAP_ENTRY_SZ;
            lemma_MulDistrib_Sub(i, slot, G_USBTDs_MAP_ENTRY_SZ);
            assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset == (i - slot) * G_USBTDs_MAP_ENTRY_SZ;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset >= G_USBTDs_MAP_ENTRY_SZ;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset <= -1 * G_USBTDs_MAP_ENTRY_SZ;
                Lemma_IntMul_EqualityOfMinusN(G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset <= 0 - G_USBTDs_MAP_ENTRY_SZ;
            }
            assert false;
        }
        assert v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
    }
}

lemma Lemma_WK_USB_TD_Map_PreserveInputParam3FieldIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires offset != G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam3) == usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam3)
{
    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures usbtd_map_get_inputparam(globals1, i, G_USBTDs_MAP_ENTRY_InputParam3) == usbtd_map_get_inputparam(globals2, i, G_USBTDs_MAP_ENTRY_InputParam3)
    {
        var v_offset := i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset;

        // Prove ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset)
        Lemma_usbtd_get_inputparams_result_is_gvar_valid_addr(AddressOfGlobal(G_USBTD_MAP_MEM()), i, v_offset);
        assert ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset);

        // Prove v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
        if(v_offset == slot * G_USBTDs_MAP_ENTRY_SZ + offset)
        {
            assert 0 - G_USBTDs_MAP_ENTRY_SZ < offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset < G_USBTDs_MAP_ENTRY_SZ;
            assert slot != i;

            assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset == i * G_USBTDs_MAP_ENTRY_SZ - slot * G_USBTDs_MAP_ENTRY_SZ;
            lemma_MulDistrib_Sub(i, slot, G_USBTDs_MAP_ENTRY_SZ);
            assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset == (i - slot) * G_USBTDs_MAP_ENTRY_SZ;

            // Show conflict
            if(i > slot)
            {
                assert i - slot >= 1;
                Lemma_NatMul_Ineq(1, i - slot, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset >= G_USBTDs_MAP_ENTRY_SZ;
            }
            else
            {
                assert i < slot;
                assert i - slot <= -1;
                Lemma_IntMul_Ineq(i - slot, -1, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset <= -1 * G_USBTDs_MAP_ENTRY_SZ;
                Lemma_IntMul_EqualityOfMinusN(G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset <= 0 - G_USBTDs_MAP_ENTRY_SZ;
            }
            assert false;
        }
        assert v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
    }
}

lemma Lemma_WK_USB_TD_Map_PreserveUSBTDContentsIfModifyOtherFields(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires (offset == G_USBTDs_MAP_ENTRY_ID_BytesOffset) ||
            (offset == G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam1_BytesOffset) || (offset == G_USBTDs_MAP_ENTRY_PID_BytesOffset) || 
            (offset == G_USBTDs_MAP_ENTRY_BUSID_BytesOffset) || (offset == G_USBTDs_MAP_ENTRY_WimpDrvSlotID_BytesOffset) || 
            (offset == G_USBTDs_MAP_ENTRY_USBPDevSlotID_BytesOffset) || (offset == G_USBTDs_MAP_ENTRY_TYPE_BytesOffset) || 
            (offset == G_USBTDs_MAP_ENTRY_eEHCISeparation_Handle_BytesOffset) || (offset == G_USBTDs_MAP_ENTRY_FLAGS_BytesOffset) || 
            (offset == G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam2_BytesOffset) || (offset == G_USBTDs_MAP_ENTRY_eEHCISeparation_InputParam3_BytesOffset)
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures forall i :: 0 <= i < USB_TD_ENTRY_NUM
                ==> p_usbtd_content_equal(globals1, globals2, i)
{
    reveal p_usbtd_content_equal();

    forall i | 0 <= i < USB_TD_ENTRY_NUM
        ensures p_usbtd_content_equal(globals1, globals2, i)
    {
        forall j | 0 <= j < MAX_USB_TD_BYTES/UINT32_BYTES
            ensures var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;
                    is_gvar_valid_addr(G_USBTD_MAP_MEM(), td_addr + j * UINT32_BYTES) &&
                    global_read_word(globals1, G_USBTD_MAP_MEM(), td_addr + j * UINT32_BYTES) == global_read_word(globals2, G_USBTD_MAP_MEM(), td_addr + j * UINT32_BYTES)
        {
            var td_addr := AddressOfGlobal(G_USBTD_MAP_MEM()) + i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset;

            var v_offset := i * G_USBTDs_MAP_ENTRY_SZ + G_USBTDs_MAP_ENTRY_TD_BytesOffset + j * UINT32_BYTES;

            // Prove ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset)
            Lemma_usbtd_slot_offset_AlwaysValidGUSBTDMapMemAddr(i, G_USBTDs_MAP_ENTRY_TD_BytesOffset + j * UINT32_BYTES);
            assert ValidGlobalOffset(G_USBTD_MAP_MEM(), v_offset);

            // Prove v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            if(v_offset == slot * G_USBTDs_MAP_ENTRY_SZ + offset)
            {
                assert 0 - G_USBTDs_MAP_ENTRY_SZ < offset - G_USBTDs_MAP_ENTRY_TD_BytesOffset - j * UINT32_BYTES < G_USBTDs_MAP_ENTRY_SZ;
                assert slot != i;

                assert offset - G_USBTDs_MAP_ENTRY_TD_BytesOffset - j * UINT32_BYTES == i * G_USBTDs_MAP_ENTRY_SZ - slot * G_USBTDs_MAP_ENTRY_SZ;
                lemma_MulDistrib_Sub(i, slot, G_USBTDs_MAP_ENTRY_SZ);
                assert offset - G_USBTDs_MAP_ENTRY_TD_BytesOffset - j * UINT32_BYTES == (i - slot) * G_USBTDs_MAP_ENTRY_SZ;

                // Show conflict
                if(i > slot)
                {
                    assert i - slot >= 1;
                    Lemma_NatMul_Ineq(1, i - slot, G_USBTDs_MAP_ENTRY_SZ);
                    assert offset - G_USBTDs_MAP_ENTRY_TD_BytesOffset - j * UINT32_BYTES >= G_USBTDs_MAP_ENTRY_SZ;
                }
                else
                {
                    assert i < slot;
                    assert i - slot <= -1;
                    Lemma_IntMul_Ineq(i - slot, -1, G_USBTDs_MAP_ENTRY_SZ);
                    assert offset - G_USBTDs_MAP_ENTRY_TD_BytesOffset - j * UINT32_BYTES <= -1 * G_USBTDs_MAP_ENTRY_SZ;
                    Lemma_IntMul_EqualityOfMinusN(G_USBTDs_MAP_ENTRY_SZ);
                    assert offset - G_USBTDs_MAP_ENTRY_TD_BytesOffset - j * UINT32_BYTES <= 0 - G_USBTDs_MAP_ENTRY_SZ;
                }
                assert false;
            }
            assert v_offset != slot * G_USBTDs_MAP_ENTRY_SZ + offset; 
        }

        Lemma_usbtd_content_equal_ProveEquivilant(globals1, globals2, i);
    }
}

lemma Lemma_WK_USB_TD_Map_PreserveOtherNonScratchpadGVarsIfModifyAnyUSBTDFields(
    globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word
)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbtd_map_valid_slot_id(slot)
    requires 0 <= offset < G_USBTDs_MAP_ENTRY_SZ
    requires var vaddr := AddressOfGlobal(G_USBTD_MAP_MEM()) + slot * G_USBTDs_MAP_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_USBTD_MAP_MEM(), vaddr) &&
            globals2 == global_write_word(globals1, G_USBTD_MAP_MEM(), vaddr, new_v)

    ensures globals_other_gvar_unchanged_2vars(globals1, globals2, G_USBTD_MAP_MEM(), G_Temp_USBTD())
{
    lemma_DistinctGlobals(); 
}