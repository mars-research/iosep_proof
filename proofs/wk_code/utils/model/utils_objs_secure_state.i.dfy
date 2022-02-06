include "utils_objs_secure_state.s.dfy"
include "../../proof/utils_os_accesses.s.dfy"
include "../../proof/utils_wimp_accesses.s.dfy"
include "../../state_properties.s.dfy"

// [TODO][Axiom][Assumption] If CanActiveEEHCIReadUSBTD holds, then the eEHCI can read the corresponding TD in the WK design
function {:axiom} EEHCIReadUSBTD_CanActiveEEHCIReadUSBTD_Property(
    s:state, 
    eehci_id_word:word, eehci_slot:word, usbtd_slot:word
) : (td_id:TD_ID)
    requires OpsSaneState(s)
    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word) &&
             var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID)
        // This predicate can be proven from other pre-conditions, but Dafny does not discover it

    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI
    requires eehci_valid_slot_id(eehci_slot)
    requires usbtd_map_valid_slot_id(usbtd_slot)

    requires var globals := wkm_get_globals(s.wk_mstate);
             CanActiveEEHCIReadUSBTD(globals, eehci_slot, usbtd_slot)
    requires var globals := wkm_get_globals(s.wk_mstate);
             TestBit(usbtd_map_get_flags(globals, usbtd_slot), USBTD_SLOT_FLAG_SlotSecure_Bit)
        // Requirement: The target USB TD must be verified and secure
    requires var globals := wkm_get_globals(s.wk_mstate);
             usbtd_map_get_pid(globals, usbtd_slot) != WS_PartitionID(PID_INVALID)
    
    ensures var globals := wkm_get_globals(s.wk_mstate);
            var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot);
            td_id == s.id_mappings.usbtd_to_td[usbtd_idword]
        // Property: The returned TD ID corresponds to the USB TD that can be read by the eEHCI
    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, {td_id}, {}, {})
        // Property: The eEHCI and the USB TD fulfills WSM_DevRead_TransfersMustBeDefinedInWSDesignModel


// [TODO][Axiom][Assumption] If EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FD/DO holds, then the eEHCI can  
// read the corresponding USBPDev's FD/DO in the WK design
lemma {:axiom} EEHCIReadUSBPDev_EEHCIAccessUSBPDevObj_ByObjID_Property(
    s:state, 
    eehci_id_word:word, eehci_slot:word, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires OpsSaneState(s)
    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word) &&
             var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID)
        // This predicate can be proven from other pre-conditions, but Dafny does not discover it

    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI
    requires eehci_valid_slot_id(eehci_slot)

    requires forall id :: id in fd_ids
                ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FD(s, eehci_slot, id)
    requires forall id :: id in do_ids
                ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_DO(s, eehci_slot, id)
        // Requirement: The access must be defined

    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, {}, fd_ids, do_ids)
        // Property: The eEHCI and the USB TD fulfills WSM_DevRead_TransfersMustBeDefinedInWSDesignModel


// [TODO][Axiom][Assumption] If EEHCIAccessObjs_ByPAddr_AccessMustBeInATransfer holds, then the eEHCI can  
// read the corresponding wimp driver's DO in the WK design
lemma {:axiom} EEHCIReadWimpDrvDO_EEHCIAccessObjs_ByPAddr_Property(
    s:state, eehci_id_word:word, eehci_slot:word, 
    read_paddr_start:paddr, read_paddr_end:uint, wimpdrv_slot:word
)
    requires OpsSaneState(s)
    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word) &&
             var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID)
        // This predicate can be proven from other pre-conditions, but Dafny does not discover it

    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI
    requires eehci_valid_slot_id(eehci_slot)

    requires read_paddr_start < read_paddr_end
    requires EEHCIAccessObjs_ByPAddr_AccessMustBeInATransfer(s, eehci_slot, read_paddr_start, read_paddr_end)
        // Requirement: The access must be defined
    requires wimpdrv_valid_slot_id(wimpdrv_slot) &&
             wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, read_paddr_start, read_paddr_end)
    requires var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
             wimpdrv_id_word != WimpDrv_ID_RESERVED_EMPTY &&
             WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word) in s.subjects.wimp_drvs
        // Requirement: Exists a wimp driver in the system that contains the memory region 
        // [read_paddr_start, read_paddr_end) in its DO

    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var wimpdrv_id_word := wimpdrv_get_id_word(wkm_get_globals(s.wk_mstate), wimpdrv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, wimpdrv_id_word);
            WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, {}, {}, {wimpdrv_do_id})
        // Property: The eEHCI and the USB TD fulfills WSM_DevRead_TransfersMustBeDefinedInWSDesignModel


// [TODO][Axiom][Assumption] If EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FD/DO holds, then the eEHCI can  
// write the corresponding USBPDev's FD/DO in the WK design
lemma {:axiom} EEHCIWriteUSBPDevObj_ByObjID_Property(
    s:state, 
    eehci_id_word:word, eehci_slot:word, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
)
    requires OpsSaneState(s)
    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word) &&
             var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID)
        // This predicate can be proven from other pre-conditions, but Dafny does not discover it

    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI
    requires eehci_valid_slot_id(eehci_slot)

    requires forall id :: id in fd_id_val_map
                ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FD(s, eehci_slot, id)
    requires forall id :: id in do_id_val_map
                ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_DO(s, eehci_slot, id)
        // Requirement: The access must be defined
    requires forall id :: id in fd_id_val_map
                ==> fd_id_val_map[id].v in usbpdev_string_range_for_fds_dos(s.subjects, EEHCIAccessUSBPDevObj_GetTargetUSBPDevID(s, id.oid), id.oid)
    requires forall id :: id in do_id_val_map
                ==> do_id_val_map[id].v in usbpdev_string_range_for_fds_dos(s.subjects, EEHCIAccessUSBPDevObj_GetTargetUSBPDevID(s, id.oid), id.oid)
        // Requirement: Writting values must be within the value ranges of these objects
        // [NOTE] We assume the entire value range of these FDs and DOs are defined in USB TDs

    ensures var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            WSM_DevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, map[], fd_id_val_map, do_id_val_map)
        // Property: The eEHCI and the USB TD fulfills WSM_DevWrite_TransfersMustBeDefinedInWSDesignModel


// [TODO][Axiom][Assumption] If EEHCIAccessObjs_ByPAddr_AccessMustBeInATransfer holds, then the eEHCI can  
// write the corresponding wimp driver's DO in the WK design
lemma {:axiom} EEHCIWriteWimpDrvDO_ByPAddr_Property(
    s:state, 
    eehci_id_word:word, eehci_slot:word,
    wimpdrv_slot:word, write_paddr_start:paddr, write_paddr_end:uint, new_val:string
)
    requires OpsSaneState(s)
    requires eehci_id_word != eEHCI_ID_INVALID &&
             var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_IsEEHCIDevID(s.subjects, dev_id)
        // Requirement: The eEHCI must exist in the system
    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_idword_in_record(globals, eehci_id_word) &&
             var dev_slot := eehci_get_slot_by_idword(globals, eehci_id_word);
             eehci_info_get_pid(globals, dev_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active
    requires var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
             WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_id.sid) 
                != WS_PartitionID(PID_INVALID)
        // This predicate can be proven from other pre-conditions, but Dafny does not discover it

    requires var globals := wkm_get_globals(s.wk_mstate);
             eehci_slot == eehci_get_slot_by_idword(globals, eehci_id_word)
        // Requirement: Because <eehci_idword_in_record> holds, the <eehci_slot> must be the slot id of the eEHCI
    requires eehci_valid_slot_id(eehci_slot)

    requires write_paddr_start < write_paddr_end
    requires EEHCIAccessObjs_ByPAddr_AccessMustBeInATransfer(s, eehci_slot, write_paddr_start, write_paddr_end)
        // Requirement: The access must be defined
    requires var globals := wkm_get_globals(s.wk_mstate);
             wimpdrv_valid_slot_id(wimpdrv_slot) &&
             wimpdrv_DO_include_mem_region(wkm_get_globals(s.wk_mstate), wimpdrv_slot, write_paddr_start, write_paddr_end) &&
             wimpdrv_get_pid(globals, wimpdrv_slot) == eehci_info_get_pid(globals, eehci_slot)
        // Requirement: Exists a wimp driver that is being accessed by the eEHCI

    requires var globals := wkm_get_globals(s.wk_mstate);
             var drv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
             WimpDrv_IDWord_ToDrvID(s.subjects, s.objects, s.id_mappings, drv_id_word) in s.subjects.wimp_drvs
        // Requirement needed by the following properties

    ensures var globals := wkm_get_globals(s.wk_mstate);
            var dev_id:Dev_ID := Map_EEHCIIDWord_ToDevID(s.subjects, s.objects, s.id_mappings, eehci_id_word);
            var drv_id_word := wimpdrv_get_id_word(globals, wimpdrv_slot);
            var wimpdrv_do_id:DO_ID := WimpDrv_GetDOID(s.subjects, s.objects, s.id_mappings, drv_id_word);
            var new_do_val:DO_Val := wimpdrv_write_do_get_do_val(s, drv_id_word, write_paddr_start, write_paddr_end, new_val);
            var do_id_val_map:map<DO_ID, DO_Val> := map[wimpdrv_do_id := new_do_val];
            WSM_DevWrite_TransfersMustBeDefinedInWSDesignModel(s, dev_id.sid, map[], map[], do_id_val_map)
        // Property: The eEHCI fulfills WSM_DevWrite_TransfersMustBeDefinedInWSDesignModel




/*********************** Utility Lemmas ********************/
lemma Lemma_EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FDs_Property(
    s:state, eehci_slot:word, fd_ids:set<FD_ID>
)
    requires ValidState(s)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(wkm_get_globals(s.wk_mstate))
    requires WK_USBTD_Map_SecureGlobalVarValues(wkm_get_globals(s.wk_mstate))

    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_info_get_pid(wkm_get_globals(s.wk_mstate), eehci_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The eEHCI must be active

    requires forall id :: id in fd_ids
                ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_FD(s, eehci_slot, id)

    ensures forall id :: id in fd_ids
                ==> id in s.objects.usbpdev_fds
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
}

lemma Lemma_EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_DOs_Property(
    s:state, eehci_slot:word, do_ids:set<DO_ID>
)
    requires ValidState(s)
    requires WK_EEHCI_Mem_SecureGlobalVarValues(wkm_get_globals(s.wk_mstate))
    requires WK_USBTD_Map_SecureGlobalVarValues(wkm_get_globals(s.wk_mstate))

    requires eehci_valid_slot_id(eehci_slot)
    requires eehci_info_get_pid(wkm_get_globals(s.wk_mstate), eehci_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The eEHCI must be active

    requires forall id :: id in do_ids
                ==> EEHCIAccessUSBPDevObj_ByObjID_AccessMustBeInATransfer_DO(s, eehci_slot, id)

    ensures forall id :: id in do_ids
                ==> id in s.objects.usbpdev_dos
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
}