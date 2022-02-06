include "usb_def.dfy"
include "../../arch/headers.dfy"
include "../../mm/wk_globals.dfy"
include "../../partition_id.s.dfy"
include "usb_tds.s.dfy"

/*********************** State Invariants and Related Predicates ********************/
predicate WK_EEHCI_Info_ValidGlobalVarValues(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    // 1. In each slot of <g_eehcis_info>, the PID is either empty or must be a wimp partition's PID
    (forall i :: eehci_valid_slot_id(i)
        ==> (eehci_info_get_pid(globals, i) == WS_PartitionID(PID_INVALID) || 
            eehci_info_get_pid(globals, i) in pids_parse_g_wimp_pids(globals))
    ) && 
        
    (true)
}

predicate WK_EEHCI_Mem_ValidGlobalVarValues(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    // 1. <g_eehci_mem> can be placed in physical memory
    (eehci_mem_pbase(globals) >= 0) &&
    (eehci_mem_pend(globals) <= ARCH_WORD_LIMIT) &&

    // 2. Each slot must map to a unique eEHCI_ID_word, unless it is eEHCI_ID_INVALID
    WK_EEHCI_Mem_ValidGlobalVarValues_IDWords(globals) &&

    // 3. In each eEHCI, if the eEHCI is inactive, then the USBTD_reg must ref no USB TDs
    (forall i :: eehci_valid_slot_id(i) && !eehci_is_active_wimp_eehci(globals, i)
        ==> EECHI_DoNotRefAnyUSBTD(globals, i)) &&

    // 4. In each eEHCI, all refed TDs must target the USB bus supported by the eEHCI
    (forall i :: eehci_valid_slot_id(i) ==> P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(globals, i)) &&

    // 5. If an EEHCI has the empty ID, then its PID must be invalid
    (forall i :: eehci_valid_slot_id(i) &&
            eehci_mem_get_eehci_id(globals, i) == eEHCI_ID_INVALID
        ==> eehci_info_get_pid(globals, i) == WS_PartitionID(PID_INVALID)
    ) &&

    (true)
}

predicate WK_EEHCI_Mem_ValidGlobalVarValues_IDWords(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
{
    // Each slot must map to a unique eEHCI_ID_word, unless it is eEHCI_ID_INVALID
    (forall i, j :: eehci_valid_slot_id(i) && eehci_valid_slot_id(j) &&
            eehci_mem_get_eehci_id(globals, i) != eEHCI_ID_INVALID && eehci_mem_get_eehci_id(globals, j) != eEHCI_ID_INVALID
        ==> (eehci_mem_get_eehci_id(globals, i) == eehci_mem_get_eehci_id(globals, j) <==> i == j)
    )
}

predicate WK_EEHCI_Mem_SecureGlobalVarValues(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_EEHCI_Mem_ValidGlobalVarValues(globals)
{
    // 1. In each eEHCI, all refed TDs must not have the ID word to be USBTD_ID_INVALID
    (forall i :: eehci_valid_slot_id(i) ==> P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveValidIDWords(globals, i)) &&

    //// 2.1 In each eEHCI, all refed TDs must have <USBTD_SLOT_FLAG_SubmitDone_Bit> and <USBTD_SLOT_FLAG_SlotSecure_Bit> set
    (forall i :: eehci_valid_slot_id(i) ==> P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags(globals, i)) &&

    //// 2.2. In each eEHCI, all refed TDs must be in the same partition with the eEHCI
    (forall i :: eehci_valid_slot_id(i) ==> P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(globals, i)) && 

    // 3. Interrupts must be disabled
    (forall i :: eehci_valid_slot_id(i) ==> eehci_mem_get_intr_enable_reg(globals, i) == eEHCI_Intr_Disable) &&
        
    (true)
}

// Predicate: In given eEHCI, all refed TDs must not have the ID word to be USBTD_ID_INVALID
predicate P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveValidIDWords(globals:globalsmap, eehci_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(eehci_slot)
{
    var eehci_pid := eehci_info_get_pid(globals, eehci_slot);

    forall usbtd_reg_id :: 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ==> (
                var usbtd_slot_id := eehci_mem_get_usbtd_reg(globals, eehci_slot, usbtd_reg_id);
                usbtd_slot_id == USBTD_SlotID_INVALID || 
                    (usbtd_map_valid_slot_id(usbtd_slot_id) &&
                        // Properties needed by the following property
                        (
                            var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot_id);

                            // In given eEHCI, all refed TDs must not have ID word to be USBTD_ID_INVALID
                            usbtd_idword != USBTD_ID_INVALID
                        )
                    )
            )
}

// Predicate: In given eEHCI, all refed TDs must have <USBTD_SLOT_FLAG_SubmitDone_Bit> and <USBTD_SLOT_FLAG_SlotSecure_Bit> set
predicate P_EEHCI_Mem_SecureGlobalVarValues_RefedTDsHaveExpectedFlags(globals:globalsmap, eehci_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(eehci_slot)
{
    forall usbtd_reg_id :: 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ==> (
                var usbtd_slot_id := eehci_mem_get_usbtd_reg(globals, eehci_slot, usbtd_reg_id);
                usbtd_slot_id == USBTD_SlotID_INVALID || 
                    (usbtd_map_valid_slot_id(usbtd_slot_id) &&
                        // Properties needed by the following property
                        (
                            var usbtd_flags := usbtd_map_get_flags(globals, usbtd_slot_id);

                            // In given eEHCI, all refed TDs must have <USBTD_SLOT_FLAG_SubmitDone_Bit> and <USBTD_SLOT_FLAG_SlotSecure_Bit> set
                            usbtd_flags == SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
                        )
                    )
            )
}

// Predicate: In given eEHCI, all refed TDs must be in the same partition with the eEHCI
predicate P_EEHCI_Mem_SecureGlobalVarValues_EEHCIAndRefedTDsSamePID(globals:globalsmap, eehci_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(eehci_slot)
{
    var eehci_pid := eehci_info_get_pid(globals, eehci_slot);

    forall usbtd_reg_id :: 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ==> (
                var usbtd_slot_id := eehci_mem_get_usbtd_reg(globals, eehci_slot, usbtd_reg_id);
                usbtd_slot_id == USBTD_SlotID_INVALID || 
                    (usbtd_map_valid_slot_id(usbtd_slot_id) &&
                        // Properties needed by the following property
                        (
                            var usbtd_pid := usbtd_map_get_pid(globals, usbtd_slot_id);

                            // In given eEHCI, all refed TDs must be in the same partition with the eEHCI
                            eehci_pid == usbtd_pid
                        )
                    )
            )
}

// Predicate: In given eEHCI, all refed TDs must target the USB bus supported by the eEHCI
predicate P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(globals:globalsmap, eehci_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(eehci_slot)
{
    var eehci_busid:uint16 := usb_parse_eehci_id(eehci_mem_get_eehci_id(globals, eehci_slot)).bus_id;

    forall usbtd_reg_id :: 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ==> (
                var usbtd_slot_id := eehci_mem_get_usbtd_reg(globals, eehci_slot, usbtd_reg_id);
                usbtd_slot_id == USBTD_SlotID_INVALID || 
                    (usbtd_map_valid_slot_id(usbtd_slot_id) &&
                     usbtd_slot_valid_busid(globals, usbtd_slot_id) &&
                        // Properties needed by the following property
                        (
                            var usbtd_busid:uint16 := usbtd_map_get_busid(globals, usbtd_slot_id);

                            // In given eEHCI, all refed TDs must target the USB bus supported by the eEHCI
                            eehci_busid == usbtd_busid
                        )
                    )
            )
}




/*********************** For g_eehcis_info ********************/
// Predicate The USB device refered by <slot> must be in <g_wimpdevs_info>
predicate eehci_valid_slot_id(slot:uint32)
{
    0 <= slot < eEHCI_INSTANCE_NUM
}

// Predicate The USB device refered by <slot> must be in <g_wimpdevs_info>
predicate eehci_is_active_wimp_eehci(globals:globalsmap, slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(slot)
{
    var eehci_pid := eehci_info_get_pid(globals, slot);

    eehci_pid != WS_PartitionID(PID_INVALID)
}

// Return the <eehci_id> field of the given WimpDrv_Info slot in <g_wimpdrvs_info>
function eehci_info_get_reserved(globals:globalsmap, slot:uint32) : word 
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr1 := AddressOfGlobal(G_EEHCIs_Info()) + slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_Info_ENTRY_Reserved_BytesOffset;
    var eehci_id := global_read_word(globals, G_EEHCIs_Info(), vaddr1);

    eehci_id
}

// Return the <pid> field of the given WimpDrv_Info slot in <g_wimpdrvs_info>
function eehci_info_get_pid(globals:globalsmap, slot:uint32) : WS_PartitionID 
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr1 := AddressOfGlobal(G_EEHCIs_Info()) + slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_INFO_ENTRY_PID_BytesOffset;
    var pid := global_read_word(globals, G_EEHCIs_Info(), vaddr1);

    WS_PartitionID(pid)
}

// Predicate: Modification to <g_eehcis_info> change the given slot only, care about the new values only
predicate eehci_info_only_change_slot_newvalue(old_globals:globalsmap, new_globals:globalsmap, slot:uint32, new_reserved:uint32, new_eehci_pid:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
{
    var vaddr1 := AddressOfGlobal(G_EEHCIs_Info()) + slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_Info_ENTRY_Reserved_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_EEHCIs_Info()) + slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_INFO_ENTRY_PID_BytesOffset;

    var d1 := is_valid_addr(vaddr1) &&
                is_valid_vaddr(vaddr1) &&   
                    // <vaddr1> must be a valid vaddr
                is_gvar_valid_vaddr(G_EEHCIs_Info(), vaddr1);
                    // <vaddr1> is a valid vaddr in <g_eehcis_info>

    if(d1) then
        var globals1 := global_write_word(old_globals, G_EEHCIs_Info(), vaddr1, new_reserved);
        var globals2 := global_write_word(globals1, G_EEHCIs_Info(), vaddr2, new_eehci_pid);

        new_globals == globals2 &&
        new_reserved == global_read_word(new_globals, G_EEHCIs_Info(), vaddr1) &&
        new_eehci_pid == global_read_word(new_globals, G_EEHCIs_Info(), vaddr2)
    else
        false
}

// Predicate: Modification to <g_eehcis_info> change the given slot only, care about both the old values and new values
predicate eehci_info_only_change_slot_oldandnewvalue(old_globals:globalsmap, new_globals:globalsmap, slot:uint32, old_reserved:uint32, old_eehci_pid:uint32, new_reserved:uint32, new_eehci_pid:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    ensures eehci_info_only_change_slot_oldandnewvalue(old_globals, new_globals, slot, old_reserved, old_eehci_pid, new_reserved, new_eehci_pid)
                ==> eehci_info_only_change_slot_newvalue(old_globals, new_globals, slot, new_reserved, new_eehci_pid)
    ensures eehci_info_only_change_slot_oldandnewvalue(old_globals, new_globals, slot, old_reserved, old_eehci_pid, new_reserved, new_eehci_pid)
                ==> (eehci_info_get_reserved(old_globals, slot) == old_reserved &&
                    eehci_info_get_pid(old_globals, slot) == WS_PartitionID(old_eehci_pid))
{
    var vaddr1 := AddressOfGlobal(G_EEHCIs_Info()) + slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_Info_ENTRY_Reserved_BytesOffset;
    var vaddr2 := AddressOfGlobal(G_EEHCIs_Info()) + slot * EEHCI_Info_ENTRY_SZ + G_EEHCI_INFO_ENTRY_PID_BytesOffset;

    var d1 := is_valid_addr(vaddr1) &&
                is_valid_vaddr(vaddr1) &&   
                    // <vaddr1> must be a valid vaddr
                is_gvar_valid_vaddr(G_EEHCIs_Info(), vaddr1);
                    // <vaddr1> is a valid vaddr in <g_eehcis_info>

    if(d1) then
        var globals1 := global_write_word(old_globals, G_EEHCIs_Info(), vaddr1, new_reserved);
        var globals2 := global_write_word(globals1, G_EEHCIs_Info(), vaddr2, new_eehci_pid);

        new_globals == globals2 &&
        old_reserved == global_read_word(old_globals, G_EEHCIs_Info(), vaddr1) &&
        old_eehci_pid == global_read_word(old_globals, G_EEHCIs_Info(), vaddr2) &&
        new_reserved == global_read_word(new_globals, G_EEHCIs_Info(), vaddr1) &&
        new_eehci_pid == global_read_word(new_globals, G_EEHCIs_Info(), vaddr2)
    else
        false
}

// Predicate: If the given eEHCI info has same state between the two global variable states
predicate {:opaque} eechi_info_equal(globals1:globalsmap, globals2:globalsmap, slot:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires eehci_valid_slot_id(slot)
{
    eehci_info_get_reserved(globals1, slot) == eehci_info_get_reserved(globals2, slot) &&
    eehci_info_get_pid(globals1, slot) == eehci_info_get_pid(globals2, slot) &&

    (true)
}





/*********************** For g_eehci_mem ********************/
// Predicate: The given eEHCI does not reference any USB TD
predicate EECHI_DoNotRefAnyUSBTD(globals:globalsmap, eehci_slot:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(eehci_slot)
{
    forall usbtd_reg_id:int :: (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
            ==> eehci_mem_get_usbtd_reg(globals, eehci_slot, usbtd_reg_id) == USBTD_SlotID_INVALID
}

// Predicate: Exists an eEHCI, the USBTD_regs of which ref the given <usbtd_slot_id>
predicate EEHCI_ExistEEHCI_RefGivenUSBTD(globals:globalsmap, eehci_slot:uint32, usbtd_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(eehci_slot)
{
    exists usbtd_reg_id :: (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS) &&
        eehci_mem_get_usbtd_reg(globals, eehci_slot, usbtd_reg_id) == usbtd_slot_id
}

// Predicate: The given eEHCI does not reference the given USB TD
predicate EECHI_DoNotRefGivenUSBTD(globals:globalsmap, eehci_slot:uint32, usbtd_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(eehci_slot)
{
    forall usbtd_reg_id:int :: (0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS)
            ==> eehci_mem_get_usbtd_reg(globals, eehci_slot, usbtd_reg_id) != usbtd_slot_id
}

// Return the <eehci_id> field of the given eEHCI memory slot in <g_eehci_mem>
function eehci_mem_get_eehci_id(globals:globalsmap, slot:uint32) : uint32
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr_id := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_ID_BytesOffset;
    var id := global_read_word(globals, G_EEHCI_MEM(), vaddr_id);

    id
}

// Return the <handle> field of the given eEHCI memory slot in <g_eehci_mem>
function eehci_mem_get_handle_reg(globals:globalsmap, slot:uint32) : uint32
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr_id := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Handle_BytesOffset;
    var v := global_read_word(globals, G_EEHCI_MEM(), vaddr_id);

    v
}

// Return the <config> reg of the given eEHCI memory slot in <g_eehci_mem>
function eehci_mem_get_config_reg(globals:globalsmap, slot:uint32) : uint32
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr_id := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset;
    var v := global_read_word(globals, G_EEHCI_MEM(), vaddr_id);

    v
}

// Return the <status> reg of the given eEHCI memory slot in <g_eehci_mem>
function eehci_mem_get_status_reg(globals:globalsmap, slot:uint32) : uint32
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr_id := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset;
    var v := global_read_word(globals, G_EEHCI_MEM(), vaddr_id);

    v
}

// Return the <intr_enable> reg of the given eEHCI memory slot in <g_eehci_mem>
function eehci_mem_get_intr_enable_reg(globals:globalsmap, slot:uint32) : uint32
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr_id := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset;
    var v := global_read_word(globals, G_EEHCI_MEM(), vaddr_id);

    v
}

// Return the <intr_target> reg of the given eEHCI memory slot in <g_eehci_mem>
function eehci_mem_get_intr_target_reg(globals:globalsmap, slot:uint32) : uint32
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr_id := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset;
    var v := global_read_word(globals, G_EEHCI_MEM(), vaddr_id);

    v
}

// Return the <usbtd_reg> reg of the given eEHCI memory slot in <g_eehci_mem>
// [NOTE] each <usbtd_reg> reg stores a USBTD slot ID
function eehci_mem_get_usbtd_reg(globals:globalsmap, eehci_slot:uint32, usbtd_reg_id:uint32) : uint32
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(eehci_slot)
    requires 0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
{
    lemma_DistinctGlobals();
    var vaddr_usbtd := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot * eEHCI_INSTANCE_BYTES + 
        G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + usbtd_reg_id * UINT32_BYTES;
    var v := global_read_word(globals, G_EEHCI_MEM(), vaddr_usbtd);

    v
}

// Return the <status> reg of the given eEHCI memory slot in <g_eehci_mem>
function eehci_mem_set_status_reg(globals:globalsmap, slot:uint32, new_v:word) : globalsmap
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(slot)
{
    lemma_DistinctGlobals();
    var vaddr_id := AddressOfGlobal(G_EEHCI_MEM()) + slot * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset;
    global_write_word(globals, G_EEHCI_MEM(), vaddr_id, new_v)
}

// Function: Return all existing eehci IDs in <g_eehci_mem>
function eehci_mem_all_existing_eehci_id_vals(globals:globalsmap) : (result:set<uint32>)
    requires WK_ValidGlobalVars_Decls(globals)

    ensures forall e :: e in result 
                <==> (exists slot :: eehci_valid_slot_id(slot) && 
                        eehci_mem_get_eehci_id(globals, slot) == e &&
                        e != eEHCI_ID_INVALID)
{
    var existing := eehci_mem_all_existing_eehci_id_vals_inner(globals, 0);

    set w | (w in existing) && (w != eEHCI_ID_INVALID)
}

// Predicate: No eEHCI refs the given USB TD (<usbtd_slot_id>) in its USBTD_reg register
predicate eehci_mem_no_ref_to_usbtd_slot(globals:globalsmap, usbtd_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(usbtd_slot_id)
{
    forall eehci_slot_id, usbtd_reg_id :: eehci_valid_slot_id(eehci_slot_id) &&
            0 <= usbtd_reg_id < eEHCI_USBTD_SlotID_NUMS
        ==> (
                var ref_usbtd_slot_id := eehci_mem_get_usbtd_reg(globals, eehci_slot_id, usbtd_reg_id);

                ref_usbtd_slot_id != usbtd_slot_id
            )
}

// Function: Clear all USBTD_regs of the given eEHCI
function eehci_mem_clear_usbtd_regs(old_globals:globalsmap, eehci_slot_id:uint32) : (new_globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(old_globals)
    
    requires eehci_valid_slot_id(eehci_slot_id)

    ensures WK_ValidGlobalVars_Decls(new_globals)
{
    var addr := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset;
    lemma_DistinctGlobals();

    var new_globals1 := global_write_at_vaddr32(old_globals, G_EEHCI_MEM(), addr, USBTD_SlotID_INVALID);
    var new_globals2 := global_write_at_vaddr32(new_globals1, G_EEHCI_MEM(), addr + 1 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals3 := global_write_at_vaddr32(new_globals2, G_EEHCI_MEM(), addr + 2 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals4 := global_write_at_vaddr32(new_globals3, G_EEHCI_MEM(), addr + 3 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals5 := global_write_at_vaddr32(new_globals4, G_EEHCI_MEM(), addr + 4 * UINT32_BYTES, USBTD_SlotID_INVALID);

    var new_globals6 := global_write_at_vaddr32(new_globals5, G_EEHCI_MEM(), addr + 5 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals7 := global_write_at_vaddr32(new_globals6, G_EEHCI_MEM(), addr + 6 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals8 := global_write_at_vaddr32(new_globals7, G_EEHCI_MEM(), addr + 7 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals9 := global_write_at_vaddr32(new_globals8, G_EEHCI_MEM(), addr + 8 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals10 := global_write_at_vaddr32(new_globals9, G_EEHCI_MEM(), addr + 9 * UINT32_BYTES, USBTD_SlotID_INVALID);

    var new_globals11 := global_write_at_vaddr32(new_globals10, G_EEHCI_MEM(), addr + 10 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals12 := global_write_at_vaddr32(new_globals11, G_EEHCI_MEM(), addr + 11 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals13 := global_write_at_vaddr32(new_globals12, G_EEHCI_MEM(), addr + 12 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals14 := global_write_at_vaddr32(new_globals13, G_EEHCI_MEM(), addr + 13 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals15 := global_write_at_vaddr32(new_globals14, G_EEHCI_MEM(), addr + 14 * UINT32_BYTES, USBTD_SlotID_INVALID);

    var new_globals16 := global_write_at_vaddr32(new_globals15, G_EEHCI_MEM(), addr + 15 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals17 := global_write_at_vaddr32(new_globals16, G_EEHCI_MEM(), addr + 16 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals18 := global_write_at_vaddr32(new_globals17, G_EEHCI_MEM(), addr + 17 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals19 := global_write_at_vaddr32(new_globals18, G_EEHCI_MEM(), addr + 18 * UINT32_BYTES, USBTD_SlotID_INVALID);
    var new_globals20 := global_write_at_vaddr32(new_globals19, G_EEHCI_MEM(), addr + 19 * UINT32_BYTES, USBTD_SlotID_INVALID);

    new_globals20
}

// Function: Clear all registers of the given eEHCI
// [NOTE] eEHCI IDs and handles are not registers
function eehci_mem_clear_all_regs(old_globals:globalsmap, eehci_slot_id:uint32) : (new_globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(old_globals)
    
    requires eehci_valid_slot_id(eehci_slot_id)

    ensures WK_ValidGlobalVars_Decls(new_globals)

    ensures eehci_mem_get_config_reg(new_globals, eehci_slot_id) == eEHCI_Config_Disable
    ensures eehci_mem_get_status_reg(new_globals, eehci_slot_id) == 0
    ensures eehci_mem_get_intr_enable_reg(new_globals, eehci_slot_id) == eEHCI_Intr_Disable
    ensures eehci_mem_get_intr_target_reg(new_globals, eehci_slot_id) == 0
    ensures forall i :: 0 <= i < eEHCI_USBTD_SlotID_NUMS ==> eehci_mem_get_usbtd_reg(new_globals, eehci_slot_id, i) == USBTD_SlotID_INVALID

    ensures forall i :: eehci_valid_slot_id(i) && i != eehci_slot_id
                ==> p_eehci_mem_equal(old_globals, new_globals, i)

    ensures globals_other_gvar_unchanged(old_globals, new_globals, G_EEHCI_MEM())
{
    reveal p_eehci_mem_equal();
    reveal p_eehci_mem_usbtd_regs_equal();

    lemma_DistinctGlobals(); 
    var new_globals1 := eehci_mem_clear_usbtd_regs(old_globals, eehci_slot_id);

    var addr2 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset;
    var new_globals2 := global_write_at_vaddr32(new_globals1, G_EEHCI_MEM(), addr2, eEHCI_Config_Disable);

    var addr3 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset;
    var new_globals3 := global_write_at_vaddr32(new_globals2, G_EEHCI_MEM(), addr3, 0);

    var addr4 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset;
    var new_globals4 := global_write_at_vaddr32(new_globals3, G_EEHCI_MEM(), addr4, eEHCI_Intr_Disable);

    var addr5 := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset;
    var new_globals5 := global_write_at_vaddr32(new_globals4, G_EEHCI_MEM(), addr5, 0);

    new_globals5
}

// Predicate: Has the given <eehci_slot> cleared all its USBTD_regs
predicate {:opaque} eehci_mem_cleared_usbtd_regs(old_globals:globalsmap, new_globals:globalsmap, eehci_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires eehci_valid_slot_id(eehci_slot_id)

    ensures eehci_mem_cleared_usbtd_regs(old_globals, new_globals, eehci_slot_id)
                ==> EECHI_DoNotRefAnyUSBTD(new_globals, eehci_slot_id)
{
    var addr := AddressOfGlobal(G_EEHCI_MEM()) + eehci_slot_id * eEHCI_INSTANCE_BYTES + G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset;
    lemma_DistinctGlobals();

    (
        var new_globals1 := eehci_mem_clear_usbtd_regs(old_globals, eehci_slot_id);

        new_globals == new_globals1
    )
}

// Predicate: Has the given <eehci_slot> cleared all its USBTD_regs
// [NOTE] eEHCI IDs and handles are not registers
predicate {:opaque} eehci_mem_cleared_all_regs(old_globals:globalsmap, new_globals:globalsmap, eehci_slot_id:uint32)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)

    requires eehci_valid_slot_id(eehci_slot_id)

    ensures eehci_mem_cleared_all_regs(old_globals, new_globals, eehci_slot_id)
                ==> EECHI_DoNotRefAnyUSBTD(new_globals, eehci_slot_id)
    ensures eehci_mem_cleared_all_regs(old_globals, new_globals, eehci_slot_id)
                ==> (
                        eehci_mem_get_config_reg(new_globals, eehci_slot_id) == eEHCI_Config_Disable &&
                        eehci_mem_get_status_reg(new_globals, eehci_slot_id) == 0 &&
                        eehci_mem_get_intr_enable_reg(new_globals, eehci_slot_id) == eEHCI_Intr_Disable &&
                        eehci_mem_get_intr_target_reg(new_globals, eehci_slot_id) == 0 &&
                        (forall i :: 0 <= i < eEHCI_USBTD_SlotID_NUMS ==> eehci_mem_get_usbtd_reg(new_globals, eehci_slot_id, i) == USBTD_SlotID_INVALID)
                )
    ensures eehci_mem_cleared_all_regs(old_globals, new_globals, eehci_slot_id)
                ==> (forall i :: eehci_valid_slot_id(i) && i != eehci_slot_id
                        ==> p_eehci_mem_equal(old_globals, new_globals, i))

    ensures eehci_mem_cleared_all_regs(old_globals, new_globals, eehci_slot_id)
                ==> globals_other_gvar_unchanged(old_globals, new_globals, G_EEHCI_MEM())
{
    new_globals == eehci_mem_clear_all_regs(old_globals, eehci_slot_id)
}

// Predicate: If the given eEHCI has same <usbtd_regs> content between the two global variable states
predicate {:opaque} p_eehci_mem_usbtd_regs_equal(globals1:globalsmap, globals2:globalsmap, slot:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires eehci_valid_slot_id(slot)
{
    forall i :: 0 <= i < eEHCI_USBTD_SlotID_NUMS
        ==> eehci_mem_get_usbtd_reg(globals1, slot, i) == eehci_mem_get_usbtd_reg(globals2, slot, i)
}

// Predicate: If the given eEHCI has same state between the two global variable states
predicate {:opaque} p_eehci_mem_equal(globals1:globalsmap, globals2:globalsmap, slot:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires eehci_valid_slot_id(slot)
{
    eehci_mem_get_eehci_id(globals1, slot) == eehci_mem_get_eehci_id(globals2, slot) &&
    eehci_mem_get_handle_reg(globals1, slot) == eehci_mem_get_handle_reg(globals2, slot) &&
    eehci_mem_get_config_reg(globals1, slot) == eehci_mem_get_config_reg(globals2, slot) &&
    eehci_mem_get_status_reg(globals1, slot) == eehci_mem_get_status_reg(globals2, slot) &&
    eehci_mem_get_intr_enable_reg(globals1, slot) == eehci_mem_get_intr_enable_reg(globals2, slot) &&
    eehci_mem_get_intr_target_reg(globals1, slot) == eehci_mem_get_intr_target_reg(globals2, slot) &&

    p_eehci_mem_usbtd_regs_equal(globals1, globals2, slot) &&

    (true)
}

// Predicate: The given <id_word> only appears at <slot> in <g_eehci_mem>
predicate p_eehci_slot_idword_unique(globals:globalsmap, slot:word, id_word:word)
    requires WK_ValidGlobalVars_Decls(globals)
    requires eehci_valid_slot_id(slot)
    requires id_word != eEHCI_ID_INVALID
{
    forall i :: eehci_valid_slot_id(i) && i != slot &&
                eehci_mem_get_eehci_id(globals, i) != eEHCI_ID_INVALID
            ==> eehci_mem_get_eehci_id(globals, i) != id_word
}

// Return the memory offsets of all <usbtd_regs>
function eehci_usbtd_regs_offsets() : set<uint32>
{
    set i | 0 <= i < eEHCI_USBTD_SlotID_NUMS :: G_EEHCI_Mem_ENTRY_USBTD_Start_BytesOffset + i * ARCH_WORD_BYTES
}

// Predicate: In the given eEHCI, exists a >usbtd_reg> refs the given USB TD slot
predicate EEHCI_ExistsUSBTDRegRefUSBTDSlot(globals:globalsmap, eehci_slot:word, target_usbtd_slot:word)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_EEHCI_Mem_ValidGlobalVarValues(globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(globals)
    requires eehci_valid_slot_id(eehci_slot)

    requires target_usbtd_slot != USBTD_SlotID_INVALID
        // Requirement: <target_usbtd_slot> must be valid

    ensures EEHCI_ExistsUSBTDRegRefUSBTDSlot(globals, eehci_slot, target_usbtd_slot)
                ==> usbtd_map_valid_slot_id(target_usbtd_slot)
    ensures EEHCI_ExistsUSBTDRegRefUSBTDSlot(globals, eehci_slot, target_usbtd_slot)
                ==> usbtd_map_get_flags(globals, target_usbtd_slot) == 
                    SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit)
{
    assert P_EEHCI_Mem_ValidGlobalVarValues_RefedTDsTargetUSBBusOfEEHCI(globals, eehci_slot);

    exists i :: 0 <= i < eEHCI_USBTD_SlotID_NUMS &&
                eehci_mem_get_usbtd_reg(globals, eehci_slot, i) == target_usbtd_slot
}




/*********************** Private Functions For g_eehci_mem ********************/
function eehci_mem_all_existing_eehci_id_vals_inner(globals:globalsmap, start:int) : (result:set<uint32>)
    requires WK_ValidGlobalVars_Decls(globals)
    requires 0 <= start <= eEHCI_INSTANCE_NUM

    ensures forall e :: e in result 
                <==> (exists slot :: start <= slot < eEHCI_INSTANCE_NUM && eehci_mem_get_eehci_id(globals, slot) == e)
    
    decreases eEHCI_INSTANCE_NUM - start
{
    if(start == eEHCI_INSTANCE_NUM) then
        {}
    else
        {eehci_mem_get_eehci_id(globals, start)} + eehci_mem_all_existing_eehci_id_vals_inner(globals, start + 1)
}