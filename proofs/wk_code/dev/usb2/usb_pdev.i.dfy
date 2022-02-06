include "usb_pdev.s.dfy"
include "usb_tds.s.dfy"
include "usb_tds_ops/usb_tds_checks.s.dfy"
include "usb_tds_ops/usb_tds_checks.i.dfy"
include "../../partition_id.i.dfy"
include "usb_pdev_nlarith.i.dfy"

/*********************** Lemma for <g_wimpdevs_info> Modification  ********************/
// Lemma: After writting <pid> field of a slot in <g_wimpdevs_info> to be PID_INVALID, the new global variable  
// satisfies P_WimpUSBPDev_ValidGlobalVarValues_PIDs
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfWrittingPIDField_NewPIDIsInvalid(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires 0 <= slot < WimpUSBPDev_Info_ENTRIES
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_v)
    
    requires new_v == PID_INVALID
    requires P_WimpUSBPDev_ValidGlobalVarValues_PIDs(old_globals)

    ensures P_WimpUSBPDev_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | 0 <= i < WimpUSBPDev_Info_ENTRIES
        ensures (usbpdev_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                usbpdev_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert usbpdev_get_pid(new_globals, i) == usbpdev_get_pid(old_globals, i) ||
               usbpdev_get_pid(new_globals, i) == WS_PartitionID(new_v);
    }
}

// Lemma: After writting <pid> field of a slot in <g_wimpdevs_info> (which USBPDev address is not invalid), the new 
// global variable satisfies P_WimpUSBPDev_ValidGlobalVarValues_PIDs
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfWrittingPIDField_USBPDevAddrIsNotInvalid(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires 0 <= slot < WimpUSBPDev_Info_ENTRIES
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_v)
    
    requires !(usbpdev_get_addr_low(old_globals, slot) == WimpUSBPDev_ADDR_EMPTY_LOW &&
             usbpdev_get_addr_high(old_globals, slot) == WimpUSBPDev_ADDR_EMPTY_HIGH)
            // Requirement: The address of the USBPDev must be valid
    
    requires WS_PartitionID(new_v) in pids_parse_g_wimp_pids(old_globals)
    requires P_WimpUSBPDev_ValidGlobalVarValues_PIDs(old_globals)

    ensures P_WimpUSBPDev_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | 0 <= i < WimpUSBPDev_Info_ENTRIES
        ensures (usbpdev_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                usbpdev_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert usbpdev_get_pid(new_globals, i) == usbpdev_get_pid(old_globals, i) ||
               usbpdev_get_pid(new_globals, i) == WS_PartitionID(new_v);
    }
}

// Lemma: After writting <pid> field a slot in <g_wimpdevs_info>, the new global variable satisfies 
// P_WimpUSBPDev_ValidGlobalVarValues_Addrs
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_HoldIfWrittingPIDField(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires global_read_fullval(old_globals, G_WimpUSBPDev_DevList()) == global_read_fullval(new_globals, G_WimpUSBPDev_DevList())

    requires 0 <= slot < WimpUSBPDev_Info_ENTRIES
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_PID_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_v)
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(old_globals)

    ensures P_WimpUSBPDev_ValidGlobalVarValues_Addrs(new_globals)
{
    forall i | 0 <= i < WimpUSBPDev_Info_ENTRIES &&
                usbpdev_get_updateflag(new_globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete
        ensures usb_is_usbpdev_addr_valid(usbpdev_get_addr(new_globals, i))
    {
        assert usbpdev_get_addr(new_globals, i) == usbpdev_get_addr(old_globals, i);
    }
}

// Lemma: After writting <update_flag> field of a slot in <g_wimpdevs_info>, the new global variable satisfies 
// P_WimpUSBPDev_ValidGlobalVarValues_PIDs
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfWrittingUpdateFlagField_WriteToUpdateComplete(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbpdev_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_v)

    requires new_v == WimpUSBPDev_Slot_UpdateFlag_Complete
    requires (usbpdev_get_addr_low(old_globals, slot) == WimpUSBPDev_ADDR_EMPTY_LOW && usbpdev_get_addr_high(old_globals, slot) == WimpUSBPDev_ADDR_EMPTY_HIGH)
            ==> usbpdev_get_pid(old_globals, slot) == WS_PartitionID(PID_INVALID)
    requires P_WimpUSBPDev_ValidGlobalVarValues_PIDs(old_globals)

    ensures P_WimpUSBPDev_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | usbpdev_valid_slot_id(i)
        ensures (usbpdev_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                usbpdev_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert usbpdev_get_pid(new_globals, i) == usbpdev_get_pid(old_globals, i);
    }
}

// Lemma: After writting <update_flag> field of a slot in <g_wimpdevs_info>, the new global variable satisfies 
// P_WimpUSBPDev_ValidGlobalVarValues_PIDs
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfWrittingUpdateFlagField_WriteToUpdating(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbpdev_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_v)
            
    requires new_v == WimpUSBPDev_Slot_UpdateFlag_Updating
    requires P_WimpUSBPDev_ValidGlobalVarValues_PIDs(old_globals)

    ensures P_WimpUSBPDev_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | usbpdev_valid_slot_id(i)
        ensures (usbpdev_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                usbpdev_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert usbpdev_get_pid(new_globals, i) == usbpdev_get_pid(old_globals, i);
    }
}

// Lemma: After writting <update_flag> field of a slot to be WimpDrv_Slot_UpdateFlag_Updating, the new global variable  
// satisfies P_WimpUSBPDev_ValidGlobalVarValues_Addrs
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_HoldIfWrittingUpdateFlagField_WriteToUpdating(
    old_globals:globalsmap, new_globals:globalsmap, slot:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires global_read_fullval(old_globals, G_WimpUSBPDev_DevList()) == global_read_fullval(new_globals, G_WimpUSBPDev_DevList())

    requires usbpdev_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, WimpUSBPDev_Slot_UpdateFlag_Updating)
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(old_globals)

    ensures P_WimpUSBPDev_ValidGlobalVarValues_Addrs(new_globals)
{
    forall i | usbpdev_valid_slot_id(i) &&
                usbpdev_get_updateflag(new_globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete
        ensures usb_is_usbpdev_addr_valid(usbpdev_get_addr(new_globals, i))
    {
        assert usbpdev_get_addr(new_globals, i) == usbpdev_get_addr(old_globals, i);
    }
}

// Lemma: After writting <update_flag> field of a slot to be WimpUSBPDev_Slot_UpdateFlag_Complete, the new global variable  
// satisfies P_WimpUSBPDev_ValidGlobalVarValues_Addrs
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_HoldIfWrittingUpdateFlagField_WriteToComplete(
    old_globals:globalsmap, new_globals:globalsmap, slot:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires global_read_fullval(old_globals, G_WimpUSBPDev_DevList()) == global_read_fullval(new_globals, G_WimpUSBPDev_DevList())

    requires usbpdev_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_UpdateFlag_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, WimpUSBPDev_Slot_UpdateFlag_Complete)
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(old_globals)

    requires usb_is_usbpdev_addr_valid(usbpdev_get_addr(old_globals, slot))
    requires forall i :: usbpdev_valid_slot_id(i) && i != slot &&
                    usbpdev_get_updateflag(old_globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete &&
                    !(usbpdev_get_addr_low(old_globals, i) == WimpUSBPDev_ADDR_EMPTY_LOW && usbpdev_get_addr_high(old_globals, i) == WimpUSBPDev_ADDR_EMPTY_HIGH)
                ==> (usbpdev_get_addr_low(old_globals, i) != usbpdev_get_addr_low(old_globals, slot) || usbpdev_get_addr_high(old_globals, i) != usbpdev_get_addr_high(old_globals, slot))

    ensures P_WimpUSBPDev_ValidGlobalVarValues_Addrs(new_globals)
{
    forall i | usbpdev_valid_slot_id(i) &&
                usbpdev_get_updateflag(new_globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete
        ensures usb_is_usbpdev_addr_valid(usbpdev_get_addr(new_globals, i))
    {
        assert usbpdev_get_addr(new_globals, i) == usbpdev_get_addr(old_globals, i);
    }
}

// Lemma: After writting <pid> field of a slot in <g_wimpdevs_info>, the new global variable  
// satisfies P_WimpUSBPDev_ValidGlobalVarValues_PIDs
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfWrittingLowAddrField(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbpdev_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_v)
    
    requires usbpdev_get_updateflag(old_globals, slot) == WimpUSBPDev_Slot_UpdateFlag_Updating
    requires P_WimpUSBPDev_ValidGlobalVarValues_PIDs(old_globals)

    ensures P_WimpUSBPDev_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | usbpdev_valid_slot_id(i)
        ensures (usbpdev_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                usbpdev_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert usbpdev_get_pid(new_globals, i) == usbpdev_get_pid(old_globals, i) ||
               usbpdev_get_pid(new_globals, i) == WS_PartitionID(new_v);
    }
}

// Lemma: After writting <low_addr> field a slot in <g_wimpdevs_info>, the new global variable satisfies 
// P_WimpUSBPDev_ValidGlobalVarValues_Addrs
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_HoldIfWrittingLowIDField_UnderFlagUpdating(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires global_read_fullval(old_globals, G_WimpUSBPDev_DevList()) == global_read_fullval(new_globals, G_WimpUSBPDev_DevList())

    requires usbpdev_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires usbpdev_get_updateflag(old_globals, slot) == WimpUSBPDev_Slot_UpdateFlag_Updating
        // Requirement: The slot is under the flag WimpUSBPDev_Slot_UpdateFlag_Updating
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_v)
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(old_globals)

    ensures P_WimpUSBPDev_ValidGlobalVarValues_Addrs(new_globals)
{
    forall i | usbpdev_valid_slot_id(i) &&
                usbpdev_get_updateflag(new_globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete
        ensures usb_is_usbpdev_addr_valid(usbpdev_get_addr(new_globals, i))
    {
        assert usbpdev_get_addr(new_globals, i) == usbpdev_get_addr(old_globals, i);
    }
}

// Lemma: After writting <high_addr> field of a slot in <g_wimpdevs_info>, the new global variable  
// satisfies P_WimpUSBPDev_ValidGlobalVarValues_PIDs
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfWrittingHighAddrField(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbpdev_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_v)
    
    requires usbpdev_get_updateflag(old_globals, slot) == WimpUSBPDev_Slot_UpdateFlag_Updating
    requires P_WimpUSBPDev_ValidGlobalVarValues_PIDs(old_globals)

    ensures P_WimpUSBPDev_ValidGlobalVarValues_PIDs(new_globals)
{
    forall i | usbpdev_valid_slot_id(i)
        ensures (usbpdev_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) || 
                usbpdev_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals))
    {
        assert usbpdev_get_pid(new_globals, i) == usbpdev_get_pid(old_globals, i) ||
               usbpdev_get_pid(new_globals, i) == WS_PartitionID(new_v);
    }
}

// Lemma: After writting <pid> field a slot in <g_wimpdevs_info>, the new global variable satisfies 
// P_WimpUSBPDev_ValidGlobalVarValues_Addrs
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_HoldIfWrittingHighIDField_UnderFlagUpdating(
    old_globals:globalsmap, new_globals:globalsmap, slot:word, new_v:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires global_read_fullval(old_globals, G_WimpUSBPDev_DevList()) == global_read_fullval(new_globals, G_WimpUSBPDev_DevList())

    requires usbpdev_valid_slot_id(slot)
    requires ValidGlobalOffset(G_WimpUSBPDev_Info(), slot * WimpUSBPDev_Info_ENTRY_SZ)
    requires usbpdev_get_updateflag(old_globals, slot) == WimpUSBPDev_Slot_UpdateFlag_Updating
        // Requirement: The slot is under the flag WimpUSBPDev_Slot_UpdateFlag_Updating
    requires var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_HighAddr_ByteOffset;
            is_valid_addr(vaddr1) && is_gvar_valid_vaddr(G_WimpUSBPDev_Info(), vaddr1) &&
            new_globals == global_write_word(old_globals, G_WimpUSBPDev_Info(), vaddr1, new_v)
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(old_globals)

    ensures P_WimpUSBPDev_ValidGlobalVarValues_Addrs(new_globals)
{
    forall i | usbpdev_valid_slot_id(i) &&
                usbpdev_get_updateflag(new_globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete
        ensures usb_is_usbpdev_addr_valid(usbpdev_get_addr(new_globals, i))
    {
        assert usbpdev_get_addr(new_globals, i) == usbpdev_get_addr(old_globals, i);
    }
}

// Lemma: If <g_wimpdevs_info> and <g_existing_pids> are unchanged, and 
// WK_WimpUSBPDev_ValidGlobalVarValues(globals1), Then WK_WimpUSBPDev_ValidGlobalVarValues(globals2)
lemma Lemma_WK_WimpUSBPDev_ValidGlobalVarValues_PreserveInNewState_IfGWimpPDevsInfoUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_WimpUSBPDev_DevList()) == global_read_fullval(globals2, G_WimpUSBPDev_DevList())
    requires global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info())
    requires global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs())
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)

    ensures WK_WimpUSBPDev_ValidGlobalVarValues(globals2)
{
    forall i | usbpdev_valid_slot_id(i)
        ensures usbpdev_get_addr(globals1, i) == usbpdev_get_addr(globals2, i)
        ensures usbpdev_get_pid(globals1, i) == usbpdev_get_pid(globals2, i)
        ensures usbpdev_get_updateflag(globals1, i) == usbpdev_get_updateflag(globals2, i)
    {
        // Dafny can automatically prove this lemma
    }
}

// Lemma: If G_USBTD_MAP_MEM, G_WimpDrvs_Info are unchanged, and no USB TD is associated with the given <usbpdev_slot>,  
// then <WK_USBTD_Map_SecureGlobalVarValues> holds
lemma Lemma_WK_USBTD_Map_SecureGlobalVarValues_HoldIfModifyingUSBPDevIsNotAssociatedWithAnyUSBTD(globals1:globalsmap, globals2:globalsmap, usbpdev_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals1)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals1)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals2)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals2)

    requires usbpdev_valid_slot_id(usbpdev_slot)
    requires usbtds_verifiedtds_do_not_associate_usb_pdev(globals1, usbpdev_slot)
        // Requirement: No USB TD is associated with the given <usbpdev_slot>
    
    requires global_read_fullval(globals1, G_USBTD_MAP_MEM()) == global_read_fullval(globals2, G_USBTD_MAP_MEM())
    requires global_read_fullval(globals1, G_WimpDrvs_Info()) == global_read_fullval(globals2, G_WimpDrvs_Info())
    requires forall i:uint32 :: usbpdev_valid_slot_id(i) && i != usbpdev_slot
        ==> p_usbpdev_slot_equal(globals1, globals2, i)
    
    ensures WK_USBTD_Map_SecureGlobalVarValues(globals2)
{
    reveal p_usbpdev_slot_equal();
    
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

        Lemma_SameUSBTDMem_Property(globals1, globals2);
        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(globals1, globals2, i);
        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals1, i);
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

        var pdev_slot := usbtd_map_get_usbpdev_slotid(globals2, i);
        var usbpdev_id := usbpdev_get_addr(globals2, pdev_slot);

        assert usbpdev_get_addr_low(globals2, pdev_slot) == usbpdev_get_addr_low(globals1, pdev_slot);
        assert usbpdev_get_addr_high(globals2, pdev_slot) == usbpdev_get_addr_high(globals1, pdev_slot);
        assert usbpdev_get_addr(globals2, pdev_slot) == usbpdev_get_addr(globals1, pdev_slot);

        assert usbtd_qh32_parse_TargetUSBPDevAddr_from_global(globals2, i) == usb_parse_usbpdev_addr(usbpdev_id);
        assert usbtd_map_get_pid(globals1, i) == usbtd_map_get_pid(globals2, i);

        Lemma_SameUSBTDMem_Property(globals1, globals2);
        Lemma_Is_USBTD_ModifyUSBPDevsAddrs_IfSecureUSBTDsAreUnchanged(globals1, globals2, i);
        assert p__usbtd_verify_qh32_step3_OnSuccessCheck(globals2, i, pdev_slot);
    }
}

// Lemma: When modifying one USBPDev slot, other slots are unmodified
lemma Lemma_WimpUSBPDev_PreserveOtherSlotsIfModifyingOneSlot(globals1:globalsmap, globals2:globalsmap, slot:uint32, offset:uint32, new_v:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)

    requires usbpdev_valid_slot_id(slot)
    requires 0 <= offset < WimpUSBPDev_Info_ENTRY_SZ
    requires var vaddr := AddressOfGlobal(G_WimpUSBPDev_Info()) + slot * WimpUSBPDev_Info_ENTRY_SZ + offset;
            is_gvar_valid_addr(G_WimpUSBPDev_Info(), vaddr) &&
            globals2 == global_write_word(globals1, G_WimpUSBPDev_Info(), vaddr, new_v)

    ensures forall i :: 0 <= i < WimpUSBPDev_Info_ENTRIES && i != slot
                ==> p_usbpdev_slot_equal(globals1, globals2, i)
{
    reveal p_usbpdev_slot_equal();

    forall i | 0 <= i < WimpUSBPDev_Info_ENTRIES && i != slot
        ensures p_usbpdev_slot_equal(globals1, globals2, i)
    {
        Lemma_usbpdev_slot_offset_AlwaysValidGUSBPDevAddr(i, WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset);        
        if(usbpdev_get_addr_low(globals1, i) != usbpdev_get_addr_low(globals2, i))
        {
            var vaddr1 := AddressOfGlobal(G_WimpUSBPDev_Info()) + i * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset;
            assert global_read_word(globals1, G_WimpUSBPDev_Info(), vaddr1) != global_read_word(globals2, G_WimpUSBPDev_Info(), vaddr1);
            assert i * WimpUSBPDev_Info_ENTRY_SZ + WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset == slot * WimpUSBPDev_Info_ENTRY_SZ + offset;
            Lemma_usbpdev_slot_offset_UniquePairForVAddr_ForContradictionProof(i, WimpUSBPDev_Info_ENTRY_LowAddr_ByteOffset, slot, offset);
            assert false;
        }
        assert usbpdev_get_addr_low(globals1, i) == usbpdev_get_addr_low(globals2, i);
    }
}

lemma Lemma_p_usbpdev_slot_equal_transitive(globals1:globalsmap, globals2:globalsmap, globals3:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires WK_ValidGlobalVars_Decls(globals3)

    requires usbpdev_valid_slot_id(slot)

    ensures  p_usbpdev_slot_equal(globals1, globals2, slot) && p_usbpdev_slot_equal(globals2, globals3, slot)
                ==> p_usbpdev_slot_equal(globals1, globals3, slot)
{
    reveal p_usbpdev_slot_equal();
}

// Lemma: If other USBPDevs' address does not equal to <new_addr_high, new_addr_low> in the old_globals, and these 
// USBPDevs are unchanged, then the predicate hold in the new_globals  
lemma Lemma_usbpdev_no_matched_addr_IfOtherUSBPDevSlotsAreUnchanged(
    old_globals:globalsmap, new_globals:globalsmap, slot:uint32, new_addr_low:word, new_addr_high:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires usbpdev_valid_slot_id(slot)
    requires forall i :: usbpdev_valid_slot_id(i) && i != slot &&
                    usbpdev_get_updateflag(old_globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete &&
                    !(usbpdev_get_addr_low(old_globals, i) == WimpUSBPDev_ADDR_EMPTY_LOW && usbpdev_get_addr_high(old_globals, i) == WimpUSBPDev_ADDR_EMPTY_HIGH)
                ==> (usbpdev_get_addr_low(old_globals, i) != new_addr_low || usbpdev_get_addr_high(old_globals, i) != new_addr_high)

    requires forall i :: 0 <= i < WimpUSBPDev_Info_ENTRIES && i != slot
                ==> p_usbpdev_slot_equal(old_globals, new_globals, i)
        
    ensures forall i :: usbpdev_valid_slot_id(i) && i != slot &&
                    usbpdev_get_updateflag(new_globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete &&
                    !(usbpdev_get_addr_low(new_globals, i) == WimpUSBPDev_ADDR_EMPTY_LOW && usbpdev_get_addr_high(new_globals, i) == WimpUSBPDev_ADDR_EMPTY_HIGH)
                ==> (usbpdev_get_addr_low(new_globals, i) != new_addr_low || usbpdev_get_addr_high(new_globals, i) != new_addr_high)
{
    reveal p_usbpdev_slot_equal();

    forall i | usbpdev_valid_slot_id(i) && i != slot &&
                    usbpdev_get_updateflag(new_globals, i) == WimpUSBPDev_Slot_UpdateFlag_Complete &&
                    !(usbpdev_get_addr_low(new_globals, i) == WimpUSBPDev_ADDR_EMPTY_LOW && usbpdev_get_addr_high(new_globals, i) == WimpUSBPDev_ADDR_EMPTY_HIGH)
        ensures usbpdev_get_addr_low(new_globals, i) != new_addr_low || usbpdev_get_addr_high(new_globals, i) != new_addr_high
    {
        assert p_usbpdev_slot_equal(old_globals, new_globals, i);
        assert usbpdev_get_updateflag(new_globals, i) == usbpdev_get_updateflag(old_globals, i);
        assert usbpdev_get_addr_low(new_globals, i) == usbpdev_get_addr_low(old_globals, i);
        assert usbpdev_get_addr_high(new_globals, i) == usbpdev_get_addr_high(old_globals, i);
    }
}




/*********************** Lemma for <g_existing_pids> Modification  ********************/
// Lemma: When replacing partition ID in <g_existing_pids>, if the old partition has no wimp drivers, and 
// P_WimpUSBPDev_ValidGlobalVarValues_PIDs(old_globals), Then P_WimpUSBPDev_ValidGlobalVarValues_PIDs(new_globals)
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_PIDs_HoldIfOverwritePIDOfPartitionHavingNoWimpDrvs(
    old_globals:globalsmap, new_globals:globalsmap, pid_vaddr:vaddr, old_pid:word, new_pid:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires is_valid_vaddr(pid_vaddr)
    requires is_gvar_valid_vaddr(G_Existing_PIDs(), pid_vaddr)
    requires !pids_is_os_pid(new_pid)
        // Requirement: <new_pid> must not be the OS partition's PID
    requires forall pid:WS_PartitionID :: pid in pids_parse_g_wimp_pids(old_globals)
            ==> (pid.v != new_pid)
        // Requirement: <new_pid> is new
    requires forall i:int :: (0 <= i < WimpUSBPDev_Info_ENTRIES)
            ==> (usbpdev_get_pid(old_globals, i) == WS_PartitionID(PID_INVALID) ||
                usbpdev_get_pid(old_globals, i) != WS_PartitionID(old_pid));
        // Requirement: The partition of the overwritten PID must do not contain any wimp usb peripheral device

    requires P_WimpUSBPDev_ValidGlobalVarValues_PIDs(old_globals)
    requires new_globals == global_write_word(old_globals, G_Existing_PIDs(), pid_vaddr, new_pid)
    requires old_pid == global_read_word(old_globals, G_Existing_PIDs(), pid_vaddr)
    
    ensures P_WimpUSBPDev_ValidGlobalVarValues_PIDs(new_globals)
{
    assert forall i :: 0 <= i < WimpUSBPDev_Info_ENTRIES
        ==> usbpdev_get_pid(old_globals, i) == usbpdev_get_pid(new_globals, i);

    forall i | 0 <= i < WimpUSBPDev_Info_ENTRIES
        ensures usbpdev_get_pid(new_globals, i) == WS_PartitionID(PID_INVALID) ||
                usbpdev_get_pid(new_globals, i) in pids_parse_g_wimp_pids(new_globals)
    {
        var old_pid_i := usbpdev_get_pid(old_globals, i);
        var new_pid_i := usbpdev_get_pid(new_globals, i);

        assert old_pid_i == new_pid_i;

        if(new_pid_i != WS_PartitionID(PID_INVALID))
        {
            Lemma_pids_parse_g_wimp_pids_CorrectnessOfSetChange(old_globals, new_globals, pid_vaddr, old_pid, new_pid);
            assert pids_parse_g_wimp_pids(new_globals) == pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)} + {WS_PartitionID(new_pid)} ||
                   pids_parse_g_wimp_pids(new_globals) == pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)};

            assert old_pid_i in pids_parse_g_wimp_pids(new_globals);
        }
    }
}




/*********************** Other Lemmas  ********************/
// Lemma: If <g_wimpdevs_info> is unchanged, and P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals1),
// Then P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals2)
lemma Lemma_P_WimpUSBPDev_ValidGlobalVarValues_Addrs_IfGWimpPDevInfoUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_WimpUSBPDev_Info()) == global_read_fullval(globals2, G_WimpUSBPDev_Info())
    requires global_read_fullval(globals1, G_WimpUSBPDev_DevList()) == global_read_fullval(globals2, G_WimpUSBPDev_DevList())
    requires P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals1)

    ensures P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals2)
{
    forall i | usbpdev_valid_slot_id(i)
        ensures usbpdev_get_addr(globals1, i) == usbpdev_get_addr(globals2, i)
        ensures usbpdev_get_updateflag(globals1, i) == usbpdev_get_updateflag(globals2, i)
    {
        // Dafny can automatically prove this lemma
    }
}