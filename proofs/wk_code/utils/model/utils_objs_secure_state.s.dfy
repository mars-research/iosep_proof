include "../../state_properties_OpsSaneStateSubset.s.dfy"
include "utils_objs_valid_state.s.dfy"
include "../../dev/usb2/usb_tds_ops/usb_tds_checks.s.dfy"

/*********************** Utility Functions - eEHCIs' Transfers ********************/
// Function: Get the TD_ID corresponding to certain eEHCI registers
function EEHCI_RegOffset_ToTDID(subjs:WSM_Subjects, objs:WSM_Objects, eehci_id:Dev_ID, offset:uint32) : (result:TD_ID)
    requires WK_ValidSubjs_eEHCIs(subjs)
    requires WK_ValidObjs_eEHCIs(subjs, objs)
    requires WSM_IsEEHCIDevID(subjs, eehci_id)
        // Requirement: The eEHCI must exist in the system

    requires offset in eehci_usbtd_regs_offsets()

    ensures result in objs.eehci_other_tds
{
    reveal WK_ValidSubjs_eEHCIs();
    reveal WK_ValidObjs_eEHCIs();
    subjs.eehcis[eehci_id].map_td_ids[offset]
}

// Function: Get the FD_ID corresponding to certain eEHCI registers
function EEHCI_RegOffset_ToFDID(subjs:WSM_Subjects, objs:WSM_Objects, eehci_id:Dev_ID, offset:uint32) : (result:FD_ID)
    requires WK_ValidSubjs_eEHCIs(subjs)
    requires WK_ValidObjs_eEHCIs(subjs, objs)
    requires WSM_IsEEHCIDevID(subjs, eehci_id)
        // Requirement: The eEHCI must exist in the system

    requires offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset ||
             offset == G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset ||
             offset == G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset

    ensures result in objs.eehci_fds
{
    reveal WK_ValidSubjs_eEHCIs();
    reveal WK_ValidObjs_eEHCIs();
    subjs.eehcis[eehci_id].map_fd_ids[offset]
}

// Function: Get the DO_ID corresponding to certain eEHCI registers
function EEHCI_RegOffset_ToDOID(subjs:WSM_Subjects, objs:WSM_Objects, eehci_id:Dev_ID, offset:uint32) : (result:DO_ID)
    requires WK_ValidSubjs_eEHCIs(subjs)
    requires WK_ValidObjs_eEHCIs(subjs, objs)
    requires WSM_IsEEHCIDevID(subjs, eehci_id)
        // Requirement: The eEHCI must exist in the system

    requires offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset

    ensures result in objs.eehci_dos
{
    reveal WK_ValidSubjs_eEHCIs();
    reveal WK_ValidObjs_eEHCIs();
    subjs.eehcis[eehci_id].map_do_ids[G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset]
}

function WSM_EEHCIRead_OwnRegsToIDs(
    s:state, eehci_id_word:word, eehci_id:Dev_ID, offset:uint32
) : (result:(set<TD_ID>, set<FD_ID>, set<DO_ID>))
    requires ValidState(s)
    requires eehci_id_word != eEHCI_ID_INVALID &&
             eehci_id == Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word) &&
             WSM_IsEEHCIDevID(s.subjects, eehci_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             SubjPID_EEHCI_ByIDWord(globals, eehci_id_word) != WS_PartitionID(PID_INVALID)
        // Requirement: The device is in the state and is active
    requires offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset || 
             offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset || offset == G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset || offset == G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset || 
             offset in eehci_usbtd_regs_offsets()

    ensures forall id :: id in result.0 ==> id in WSM_AllTDIDs(s.objects)
    ensures forall id :: id in result.1 ==> id in WSM_AllFDIDs(s.objects)
    ensures forall id :: id in result.2 ==> id in WSM_AllDOIDs(s.objects)
{
    if(offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset) then
        var target_do_id := EEHCI_RegOffset_ToDOID(s.subjects, s.objects, eehci_id, offset);
        ({}, {}, {target_do_id})
    else if (offset == G_EEHCI_Mem_ENTRY_EECHI_Config_BytesOffset || offset == G_EEHCI_Mem_ENTRY_EECHI_IntrEnable_BytesOffset || offset == G_EEHCI_Mem_ENTRY_EECHI_IntrTarget_BytesOffset) then
        var target_fd_id := EEHCI_RegOffset_ToFDID(s.subjects, s.objects, eehci_id, offset);
        ({}, {target_fd_id}, {})
    else
        assert offset in eehci_usbtd_regs_offsets();
        var target_td_id := EEHCI_RegOffset_ToTDID(s.subjects, s.objects, eehci_id, offset);
        ({target_td_id}, {}, {})
}

function WSM_EEHCIWriteOwnDO_OwnRegsToIDsVals(
    s:state, eehci_id_word:word, eehci_id:Dev_ID, offset:uint32, new_val:word
) : (result:(map<TD_ID, TD_Val>, map<FD_ID, FD_Val>, map<DO_ID, DO_Val>))
    requires ValidState(s)
    requires eehci_id_word != eEHCI_ID_INVALID &&
             eehci_id == Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word) &&
             WSM_IsEEHCIDevID(s.subjects, eehci_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             SubjPID_EEHCI_ByIDWord(globals, eehci_id_word) != WS_PartitionID(PID_INVALID)
        // Requirement: The device is in the state and is active
    requires offset == G_EEHCI_Mem_ENTRY_EECHI_Status_BytesOffset

    ensures result.0 == map[]
    ensures result.1 == map[]
    ensures forall id :: id in result.2 ==> id in WSM_AllDOIDs(s.objects)
    ensures forall id :: id in result.2 ==> id in s.subjects.eehcis[eehci_id].do_ids
{
    var do_id := EEHCI_RegOffset_ToDOID(s.subjects, s.objects, eehci_id, offset);
    var do_id_val_map:map<DO_ID, DO_Val> := map[do_id := DO_Val(DevWrite_WordToString(new_val))];

    (map[], map[], do_id_val_map)
}

// Predicate: Can an active eEHCI reads the given USB TD 
predicate CanActiveEEHCIReadUSBTD(globals:globalsmap, eehci_slot:word, target_usbtd_slot:word)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_EEHCI_Mem_ValidGlobalVarValues(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(globals)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals)

    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_info_get_pid(globals, eehci_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The eEHCI must be active

    requires target_usbtd_slot != USBTD_SlotID_INVALID
        // Requirement: <target_usbtd_slot> must be valid
{
    reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
    reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();

    exists usbtd_slots:seq<word> :: |usbtd_slots| >= 1 &&
        (forall i :: 0 <= i < |usbtd_slots| - 1 ==> usbtd_map_valid_slot_id(usbtd_slots[i])) &&
                                            // Valid USB TD slot before the <target_usbtd_slot>
        usbtd_slots[|usbtd_slots| - 1] == target_usbtd_slot && // last USB TD is the target USB TD (<target_usbtd_slot>)
        EEHCI_ExistsUSBTDRegRefUSBTDSlot(globals, eehci_slot, usbtd_slots[0]) &&
                                            // Some eEHCI usbtd_reg refs the first USB TD
        (forall i :: 0 <= i < |usbtd_slots| - 1 ==> usbtd_is_slot_ref_target_slot(globals, usbtd_slots[i], usbtd_slots[i+1]))
                                            // Current USB TD always links the next USB TD
}

// Predicate: For the operation <EEHCIRead/WriteUSBPDevObj_ByObjID>, the access must be defined in a USB TD that can be 
// read by the eEHCI
// [HW] Axiom: qTDs do not define any transfers to USBPDevs. Instead, these transfers are defined in QHs linking these qTDs.
// This axiom makes sense, even though it is not the case in reality. This is because (1) only QHs can link qTDs, and 
// (2) QHs define the target USBPDev, and (3) transfers to USBPDevs defined in qTDs target the same device as defined in the QHs,
// Thus, this axiom does not omit any transfers to USBPDevs in fact, and simplify the specifications
predicate EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FD(
    s:state, eehci_slot:word, fd_id:FD_ID
)
    requires ValidState(s)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(wkm_get_globals(s.wk_mstate))
    requires WK_USBTD_Map_SecureGlobalVarValues(wkm_get_globals(s.wk_mstate))

    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_info_get_pid(wkm_get_globals(s.wk_mstate), eehci_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The eEHCI must be active
{
    var globals := wkm_get_globals(s.wk_mstate);
    assert P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals);

    exists usbtd_slot:word :: usbtd_slot != USBTD_SlotID_INVALID &&
        (
            Lemma_CanActiveEEHCIReadUSBTD_ProveProperty(globals, eehci_slot, usbtd_slot);
            CanActiveEEHCIReadUSBTD(globals, eehci_slot, usbtd_slot)
                // Exist a USB TD, and the eEHCI can read the USB TD
        ) &&
        usbtd_map_get_type(globals, usbtd_slot) == USBTDs_TYPE_QH32 &&      // [TODO] Not support iTD and siTD yet
            // The USB TD cannot be a qTD
        (
            var usbpdev_slot := usbtd_map_get_usbpdev_slotid(globals, usbtd_slot);
            var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_get_addr(globals, usbpdev_slot));
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);

            WSM_IsUSBPDevID(s.subjects, usbpdev_id) &&
                // The USBPDev must exist in the system
            (fd_id in s.subjects.usbpdevs[usbpdev_id].fd_ids)
                // And the object <fd_id> must be the USBPDev's FDs
        )
}

// Predicate: For the operation <EEHCIRead/WriteUSBPDevObj_ByObjID>, the access must be defined in a USB TD that can be 
// read by the eEHCI
// [NOTE] This predicate is based on the same axiom with <EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FD>
predicate EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_DO(
    s:state, eehci_slot:word, do_id:DO_ID
)
    requires ValidState(s)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(wkm_get_globals(s.wk_mstate))
    requires WK_USBTD_Map_SecureGlobalVarValues(wkm_get_globals(s.wk_mstate))

    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_info_get_pid(wkm_get_globals(s.wk_mstate), eehci_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The eEHCI must be active
{
    var globals := wkm_get_globals(s.wk_mstate);
    assert P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals);

    exists usbtd_slot:word :: usbtd_slot != USBTD_SlotID_INVALID &&
        (
            Lemma_CanActiveEEHCIReadUSBTD_ProveProperty(globals, eehci_slot, usbtd_slot);
            CanActiveEEHCIReadUSBTD(globals, eehci_slot, usbtd_slot)
                // Exist a USB TD, and the eEHCI can read the USB TD
        ) &&
        usbtd_map_get_type(globals, usbtd_slot) == USBTDs_TYPE_QH32 &&      // [TODO] Not support iTD and siTD yet
            // The USB TD cannot be a qTD
        (
            var usbpdev_slot := usbtd_map_get_usbpdev_slotid(globals, usbtd_slot);
            var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_get_addr(globals, usbpdev_slot));
            var usbpdev_id:Dev_ID := Map_USBPDevAddr_ToDevID(s.subjects, s.objects, s.id_mappings, usbpdev_addr);

            WSM_IsUSBPDevID(s.subjects, usbpdev_id) &&
                // The USBPDev must exist in the system
            (do_id in s.subjects.usbpdevs[usbpdev_id].do_ids)
                // And the object <do_id> must be the USBPDev's DOs
        )
}

// In EEHCIReadUSBPDevObj_ByObjID/EEHCIWriteUSBPDevObj_ByObjID operations, return the USBPDev ID that owns the object 
// <o_id>
function EEHCIAccessUSBPDevObj_GetTargetUSBPDevID(s:state, o_id:Object_ID) : Dev_ID
    requires exists usbpdev_id :: WSM_IsUSBPDevID(s.subjects, usbpdev_id) &&
             (FD_ID(o_id) in s.subjects.usbpdevs[usbpdev_id].fd_ids || DO_ID(o_id) in s.subjects.usbpdevs[usbpdev_id].do_ids)

    ensures WSM_IsUSBPDevID(s.subjects, EEHCIAccessUSBPDevObj_GetTargetUSBPDevID(s, o_id))
{
    var usbpdev_id :| WSM_IsUSBPDevID(s.subjects, usbpdev_id) &&
             (FD_ID(o_id) in s.subjects.usbpdevs[usbpdev_id].fd_ids || DO_ID(o_id) in s.subjects.usbpdevs[usbpdev_id].do_ids);

    usbpdev_id
}

// Predicate: Is [access_paddr_start, access_paddr_end) inside one of the multiple buffer regions defined in a USB TD
// [NOTE] We can regard eEHCIs issue several transfers, each for an individual buffer region defined in a USB TD
predicate usbtd_is_paddr_region_within_one_buffer_region(
    globals:globalsmap, td_slot:uint32, access_paddr_start:paddr, access_paddr_end:uint
)
    requires WK_ValidGlobalVars_Decls(globals)
    requires usbtd_map_valid_slot_id(td_slot)

    requires usbtd_map_get_type(globals, td_slot) == USBTDs_TYPE_QTD32 || usbtd_map_get_type(globals, td_slot) == USBTDs_TYPE_QH32
        // [TODO] Not support iTD and siTD yet

    requires access_paddr_start <= access_paddr_end
{
    var td_type := usbtd_map_get_type(globals, td_slot);

    if(td_type == USBTDs_TYPE_QTD32) then
        var buf_regions := usbtd_qtd32_parse_DataBufPtrs_from_global(globals, td_slot);
        is_mem_region_inside(buf_regions.0, buf_regions.0 + PAGE_4K_SZ, access_paddr_start, access_paddr_end) ||
        is_mem_region_inside(buf_regions.1, buf_regions.1 + PAGE_4K_SZ, access_paddr_start, access_paddr_end) ||
        is_mem_region_inside(buf_regions.2, buf_regions.2 + PAGE_4K_SZ, access_paddr_start, access_paddr_end) ||
        is_mem_region_inside(buf_regions.3, buf_regions.3 + PAGE_4K_SZ, access_paddr_start, access_paddr_end) ||
        is_mem_region_inside(buf_regions.4, buf_regions.4 + PAGE_4K_SZ, access_paddr_start, access_paddr_end)
    else // if(td_type == USBTDs_TYPE_QH32) then
        var buf_regions := usbtd_qh32_parse_DataBufPtrs_from_global(globals, td_slot);
        is_mem_region_inside(buf_regions.0, buf_regions.0 + PAGE_4K_SZ, access_paddr_start, access_paddr_end) ||
        is_mem_region_inside(buf_regions.1, buf_regions.1 + PAGE_4K_SZ, access_paddr_start, access_paddr_end) ||
        is_mem_region_inside(buf_regions.2, buf_regions.2 + PAGE_4K_SZ, access_paddr_start, access_paddr_end) ||
        is_mem_region_inside(buf_regions.3, buf_regions.3 + PAGE_4K_SZ, access_paddr_start, access_paddr_end) ||
        is_mem_region_inside(buf_regions.4, buf_regions.4 + PAGE_4K_SZ, access_paddr_start, access_paddr_end)
}

// Predicate: For the operation <EEHCIRead/WriteObjs_ByPAddr>, the access must be defined in a USB TD that can be 
// read by the eEHCI
// [Assumption] As each USB TD contains multiple buffer regions (e.g., qTD32 contains five buffer regions), eEHCIs
// only read/write one buffer in one access. In other words, eEHCIs issue separate accesses for different buffers.
predicate EEHCIAccessObjs_ByPAddr_AccessMustBeInATransfer(
    s:state, eehci_slot:word, access_paddr_start:paddr, access_paddr_end:uint
)
    requires ValidState(s)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(wkm_get_globals(s.wk_mstate))
    requires WK_USBTD_Map_SecureGlobalVarValues(wkm_get_globals(s.wk_mstate))

    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_info_get_pid(wkm_get_globals(s.wk_mstate), eehci_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The eEHCI must be active

    requires access_paddr_start <= access_paddr_end
{
    var globals := wkm_get_globals(s.wk_mstate);
    assert P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals);

    exists usbtd_slot:word :: usbtd_slot != USBTD_SlotID_INVALID &&
        (
            Lemma_CanActiveEEHCIReadUSBTD_ProveProperty(globals, eehci_slot, usbtd_slot);
            CanActiveEEHCIReadUSBTD(globals, eehci_slot, usbtd_slot)
            // Exist a USB TD, and the eEHCI can read the USB TD
        ) &&
        (usbtd_map_get_type(globals, usbtd_slot) == USBTDs_TYPE_QTD32 || usbtd_map_get_type(globals, usbtd_slot) == USBTDs_TYPE_QH32) &&  
            // [TODO] Not support iTD and siTD yet
        usbtd_is_paddr_region_within_one_buffer_region(globals, usbtd_slot, access_paddr_start, access_paddr_end)
            // And [access_paddr_start, access_paddr_end) must be inside one of the multiple buffer regions defined in 
            // the USB TD
}




/*********************** Private Lemmas ********************/
lemma Lemma_CanActiveEEHCIReadUSBTD_ProveProperty(globals:globalsmap, eehci_slot:word, target_usbtd_slot:word)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_EEHCI_Mem_ValidGlobalVarValues(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(globals)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals)

    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_info_get_pid(globals, eehci_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The eEHCI must be active

    requires target_usbtd_slot != USBTD_SlotID_INVALID
        // Requirement: <target_usbtd_slot> must be valid

    ensures CanActiveEEHCIReadUSBTD(globals, eehci_slot, target_usbtd_slot)
                ==> usbtd_map_valid_slot_id(target_usbtd_slot)
    ensures CanActiveEEHCIReadUSBTD(globals, eehci_slot, target_usbtd_slot)
                ==> TestBit(usbtd_map_get_flags(globals, target_usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
    ensures CanActiveEEHCIReadUSBTD(globals, eehci_slot, target_usbtd_slot)
                ==> (
                        var usbpdev_slot := usbtd_map_get_usbpdev_slotid(globals, target_usbtd_slot);
                        usbtd_map_get_type(globals, target_usbtd_slot) == USBTDs_TYPE_QH32
                            ==> usb_is_usbpdev_addr_valid(usbpdev_get_addr(globals, usbpdev_slot))
                    )
        // Property: If <target_usbtd_slot> is a QH, then its stored USBPDev slot must have a valid USBPDev address
    ensures CanActiveEEHCIReadUSBTD(globals, eehci_slot, target_usbtd_slot)
                ==> (
                        var usbpdev_slot := usbtd_map_get_usbpdev_slotid(globals, target_usbtd_slot);
                        var addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
                        usb_is_usbpdev_addr_valid(addr) &&
                        (usbtd_map_get_type(globals, target_usbtd_slot) == USBTDs_TYPE_QH32
                            ==> (var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_get_addr(globals, usbpdev_slot));
                                usbpdev_addr != usb_parse_usbpdev_addr(addr))
                        )
                    )
        // Property 4: The USBPDevAddr associated with the <target_usbtd_slot> must not be empty
    ensures CanActiveEEHCIReadUSBTD(globals, eehci_slot, target_usbtd_slot)
                ==> eehci_info_get_pid(globals, eehci_slot) == usbtd_map_get_pid(globals, target_usbtd_slot)
        // Property: eEHCI and the target USB TD must be in the same partition
{
    if(CanActiveEEHCIReadUSBTD(globals, eehci_slot, target_usbtd_slot))
    {
        var usbtd_slots:seq<word> :| |usbtd_slots| >= 1 &&
            (forall i :: 0 <= i < |usbtd_slots| - 1 ==> usbtd_map_valid_slot_id(usbtd_slots[i])) &&
                                                // Valid USB TD slot before the <target_usbtd_slot>
            usbtd_slots[|usbtd_slots| - 1] == target_usbtd_slot && // last USB TD is the target USB TD (<target_usbtd_slot>)
            EEHCI_ExistsUSBTDRegRefUSBTDSlot(globals, eehci_slot, usbtd_slots[0]) &&
                                                // Some eEHCI usbtd_reg refs the first USB TD
            (forall i :: 0 <= i < |usbtd_slots| - 1 ==> usbtd_is_slot_ref_target_slot(globals, usbtd_slots[i], usbtd_slots[i+1]));
                                                // Current USB TD always links the next USB TD

        Lemma_CanActiveEEHCIReadUSBTD_ProveProperty_inner(globals, eehci_slot, usbtd_slots, target_usbtd_slot);
    }
}

lemma Lemma_CanActiveEEHCIReadUSBTD_ProveProperty_inner(globals:globalsmap, eehci_slot:word, usbtd_slots:seq<word>, target_usbtd_slot:word)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_EEHCI_Mem_ValidGlobalVarValues(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(globals)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals)

    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_info_get_pid(globals, eehci_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The eEHCI must be active

    requires target_usbtd_slot != USBTD_SlotID_INVALID
        // Requirement: <target_usbtd_slot> must be valid

    requires |usbtd_slots| >= 1 &&
        (forall i :: 0 <= i < |usbtd_slots| - 1 ==> usbtd_map_valid_slot_id(usbtd_slots[i])) &&
                                            // Valid USB TD slot before the <target_usbtd_slot>
        usbtd_slots[|usbtd_slots| - 1] == target_usbtd_slot && // last USB TD is the target USB TD (<target_usbtd_slot>)
        EEHCI_ExistsUSBTDRegRefUSBTDSlot(globals, eehci_slot, usbtd_slots[0]) &&
                                            // Some eEHCI usbtd_reg refs the first USB TD
        (forall i :: 0 <= i < |usbtd_slots| - 1 ==> usbtd_is_slot_ref_target_slot(globals, usbtd_slots[i], usbtd_slots[i+1]))
                                            // Current USB TD always links the next USB TD

    ensures usbtd_map_valid_slot_id(target_usbtd_slot)
    ensures TestBit(usbtd_map_get_flags(globals, target_usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
    ensures var usbpdev_slot := usbtd_map_get_usbpdev_slotid(globals, target_usbtd_slot);
            usbtd_map_get_type(globals, target_usbtd_slot) == USBTDs_TYPE_QH32
                ==> usb_is_usbpdev_addr_valid(usbpdev_get_addr(globals, usbpdev_slot))
        // Property 3: If <target_usbtd_slot> is a QH, then its stored USBPDev slot must have a valid USBPDev address
    ensures var usbpdev_slot := usbtd_map_get_usbpdev_slotid(globals, target_usbtd_slot);
            var addr := UInt64_FromTwoUInt32s(WimpUSBPDev_ADDR_EMPTY_HIGH, WimpUSBPDev_ADDR_EMPTY_LOW);
            usb_is_usbpdev_addr_valid(addr) &&
            (usbtd_map_get_type(globals, target_usbtd_slot) == USBTDs_TYPE_QH32
                ==> (var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_get_addr(globals, usbpdev_slot));
                    usbpdev_addr != usb_parse_usbpdev_addr(addr))
            )
        // Property 4: The USBPDevAddr associated with the <target_usbtd_slot> must not be empty
    ensures eehci_info_get_pid(globals, eehci_slot) == usbtd_map_get_pid(globals, target_usbtd_slot)
        // Property 5: eEHCI and the target USB TD must be in the same partition
{
    // Prove the eEHCI can read all intermediate USB TD
    Lemma_CanActiveEEHCIReadUSBTD_EEHCICanReadAllIntermediateUSBTDs(globals, eehci_slot, usbtd_slots, target_usbtd_slot);

    if(|usbtd_slots| == 1)
    {
        assert EEHCI_ExistsUSBTDRegRefUSBTDSlot(globals, eehci_slot, target_usbtd_slot);

        reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();

        assert P_WimpUSBPDev_ValidGlobalVarValues_Addrs(globals);
        assert usbtd_map_get_flags(globals, target_usbtd_slot) == 
                    SetBit(SetBit(0, USBTD_SLOT_FLAG_SubmitDone_Bit), USBTD_SLOT_FLAG_SlotSecure_Bit);
        Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);

        // Prove property 5
        Lemma_usb_is_usbpdev_addr_valid_ValidIfAddrIsEmpty(); 
    }
    else
    {
        assert |usbtd_slots| > 1;

        var next_target_usbtd_slot := usbtd_slots[|usbtd_slots| - 2];
        var next_usbtd_slots := usbtd_slots[..|usbtd_slots|-1];
        Lemma_CanActiveEEHCIReadUSBTD_ProveProperty_inner(globals, eehci_slot, next_usbtd_slots, next_target_usbtd_slot);

        // Prove the relationship between <next_target_usbtd_slot> and <target_usbtd_slot>
        Lemma_CanActiveEEHCIReadUSBTD_ProveProperty_Private_ProveLastSecondUSBTDRefsLastUSBTD(globals, usbtd_slots, next_target_usbtd_slot, target_usbtd_slot);
        assert usbtd_is_slot_ref_target_slot(globals, next_target_usbtd_slot, target_usbtd_slot);

        assert usbtd_map_valid_slot_id(next_target_usbtd_slot);

        reveal p__usbtd_verify_qtd32_step1_OnSuccessCheck();
        reveal p__usbtd_verify_qtd32_step2_OnSuccessCheck();
        reveal p__usbtd_verify_qh32_step1_OnSuccessCheck();
        reveal p__usbtd_verify_qh32_step2_OnSuccessCheck();
        reveal p__usbtd_verify_qh32_step3_OnSuccessCheck();

        assert usbtd_slot_valid_type(globals, next_target_usbtd_slot);
        assert usbtd_map_get_type(globals, next_target_usbtd_slot) == USBTDs_TYPE_QTD32 || usbtd_map_get_type(globals, next_target_usbtd_slot) == USBTDs_TYPE_QH32 ||
                usbtd_map_get_type(globals, next_target_usbtd_slot) == USBTDs_TYPE_iTD32 || usbtd_map_get_type(globals, next_target_usbtd_slot) == USBTDs_TYPE_siTD32;

        Lemma_TestBit_ReturnTrueIfANumberSetBit(USBTD_SLOT_FLAG_SlotSecure_Bit);
        assert TestBit(usbtd_map_get_flags(globals, next_target_usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit);
        assert WK_USBTD_Map_SecureGlobalVarValues_qTD32(globals, next_target_usbtd_slot) || WK_USBTD_Map_SecureGlobalVarValues_qh32(globals, next_target_usbtd_slot) || 
                WK_USBTD_Map_SecureGlobalVarValues_iTD32(globals, next_target_usbtd_slot) || WK_USBTD_Map_SecureGlobalVarValues_siTD32(globals, next_target_usbtd_slot);

        assert TestBit(usbtd_map_get_flags(globals, target_usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit);

        // Prove eehci_info_get_pid(globals, eehci_slot) == usbtd_map_get_pid(globals, target_usbtd_slot)
        assert usbtd_map_get_pid(globals, next_target_usbtd_slot) == usbtd_map_get_pid(globals, target_usbtd_slot);
    }
}

// Lemma: If an active eEHCI (<eehci_slot>) can read a USB TD (<target_usbtd_slot>) via a sequence of active 
// intermediate USB TDs (<usbtd_slots>), then the device can read all these USB TDs 
lemma Lemma_CanActiveEEHCIReadUSBTD_EEHCICanReadAllIntermediateUSBTDs(
    globals:globalsmap, eehci_slot:word, usbtd_slots:seq<word>, target_usbtd_slot:word
)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_EEHCI_Mem_ValidGlobalVarValues(globals)
    requires WK_USBTD_Map_ValidGlobalVarValues(globals)
    requires WK_WimpUSBPDev_ValidGlobalVarValues(globals)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(globals)
    requires WK_USBTD_Map_SecureGlobalVarValues(globals)

    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_info_get_pid(globals, eehci_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The eEHCI must be active

    requires target_usbtd_slot != USBTD_SlotID_INVALID
        // Requirement: <target_usbtd_slot> must be valid

    requires |usbtd_slots| >= 1 &&
        (forall i :: 0 <= i < |usbtd_slots| - 1 ==> usbtd_map_valid_slot_id(usbtd_slots[i])) &&
                                            // Valid USB TD slot before the <target_usbtd_slot>
        usbtd_slots[|usbtd_slots| - 1] == target_usbtd_slot && // last USB TD is the target USB TD (<target_usbtd_slot>)
        EEHCI_ExistsUSBTDRegRefUSBTDSlot(globals, eehci_slot, usbtd_slots[0]) &&
                                            // Some eEHCI usbtd_reg refs the first USB TD
        (forall i :: 0 <= i < |usbtd_slots| - 1 ==> usbtd_is_slot_ref_target_slot(globals, usbtd_slots[i], usbtd_slots[i+1]))
                                            // Current USB TD always links the next USB TD
        // Rquirement: The eEHCI (<eehci_slot>) can read the USB TD by following this chain

    ensures forall td_id2 :: td_id2 in usbtd_slots
                ==> CanActiveEEHCIReadUSBTD(globals, eehci_slot, td_id2)
{
    var i := 0;
    var new_td_ids := usbtd_slots[..i+1]; 

    while (i < |usbtd_slots|)
        invariant i <= |usbtd_slots|

        invariant forall td_id2 :: td_id2 in usbtd_slots[..i]
                    ==> CanActiveEEHCIReadUSBTD(globals, eehci_slot, td_id2)
    {
        var new_td_ids := usbtd_slots[..i+1];

        i := i + 1;
    }
}

lemma Lemma_CanActiveEEHCIReadUSBTD_ProveProperty_Private_ProveLastSecondUSBTDRefsLastUSBTD(globals:globalsmap, usbtd_slots:seq<word>, usbtd_slot:word, target_usbtd_slot:word)
    requires WK_ValidGlobalVars_Decls(globals)

    requires |usbtd_slots| > 1
    requires (forall i :: 0 <= i < |usbtd_slots| - 1 ==> usbtd_map_valid_slot_id(usbtd_slots[i]))
    requires (forall i :: 0 <= i < |usbtd_slots| - 1 ==> usbtd_is_slot_ref_target_slot(globals, usbtd_slots[i], usbtd_slots[i+1]))
    requires usbtd_slots[|usbtd_slots| - 1] == target_usbtd_slot
    requires usbtd_slot == usbtd_slots[|usbtd_slots| - 2]

    ensures usbtd_is_slot_ref_target_slot(globals, usbtd_slot, target_usbtd_slot)
{
    assert (forall i :: 0 <= i < |usbtd_slots| - 1 ==> usbtd_is_slot_ref_target_slot(globals, usbtd_slots[i], usbtd_slots[i+1]));

    if(!usbtd_is_slot_ref_target_slot(globals, usbtd_slots[|usbtd_slots| - 2], usbtd_slots[|usbtd_slots| - 1]))
    {
        var i := |usbtd_slots| - 2;
        assert usbtd_is_slot_ref_target_slot(globals, usbtd_slots[i], usbtd_slots[i+1]);
        assert false;
    }
}