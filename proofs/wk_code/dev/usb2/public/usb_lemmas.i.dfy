include "../../../state_properties_OpsSaneStateSubset.s.dfy" 
include "../../../state_properties_validity.i.dfy"

// Lemma: Registered and active wimp drivers must exist in the system
lemma Lemma_USBTD_ExistInSystem_IfRegisteredAndActive(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, usbtd_slot:word
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires usbtd_map_valid_slot_id(usbtd_slot)
    requires usbtd_map_get_pid(globals, usbtd_slot) != WS_PartitionID(PID_INVALID)
        // Requirement: The USB TD must be registered and is active

    ensures var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot);
            usbtd_idword in id_mappings.usbtd_to_td &&
            usbtd_idword in id_mappings.usbtd_to_fd &&
            usbtd_idword in id_mappings.usbtd_to_do
        // Property: Properties needed by the following property
    ensures var usbtd_idword := usbtd_map_get_idword(globals, usbtd_slot);
            var usbtd_td_id:TD_ID := id_mappings.usbtd_to_td[usbtd_idword];
            var usbtd_fd_id:FD_ID := id_mappings.usbtd_to_fd[usbtd_idword];
            var usbtd_do_id:DO_ID := id_mappings.usbtd_to_do[usbtd_idword];
            usbtd_td_id in objs.usbtd_tds &&
            usbtd_fd_id in objs.usbtd_fds &&
            usbtd_do_id in objs.usbtd_dos
{
    reveal WK_ValidGlobalVarValues_ActiveUSBTDs();

    Lemma_WK_USBTD_Map_ValidGlobalVarValues_P1_Equivilant(globals); 
    Lemma_ValidState_ImpliesWK_ValidGlobalVarValues_ActiveUSBTDs(subjs, objs, id_mappings, globals);
}

// Lemma: Registered and active USB peripheral devices must exist in the system
lemma Lemma_USBPDevs_ExistInSystem_IfRegisteredAndActive(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, usbpdev_slot:word
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidGlobalVarValues_USBPDevs(subjs, globals)
    requires WK_ValidGlobalVarValues_USBPDevList(subjs, id_mappings, globals)

    requires usbpdev_valid_slot_id(usbpdev_slot)
    requires usbpdev_get_pid(globals, usbpdev_slot) != WS_PartitionID(PID_INVALID)
    requires usbpdev_get_updateflag(globals, usbpdev_slot) == WimpUSBPDev_Slot_UpdateFlag_Complete
        // Requirement: The USBPDev must be registered and is active

    ensures var usbpdev_addr_raw:uint64 := usbpdev_get_addr(globals, usbpdev_slot);
            var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
            usbpdev_addr in id_mappings.usbpdev_ids &&
            id_mappings.usbpdev_ids[usbpdev_addr] in subjs.usbpdevs
{
    reveal WK_ValidGlobalVarValues_USBPDevs();
    reveal WK_ValidGlobalVarValues_USBPDevList();
}

// Lemma: For each USBPDev, its internal FDs and DOs have the same PID with the device
lemma Lemma_USBPDev_InternalFDsAndDOsHaveSamePIDWithDevice(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, usbpdev_id:Dev_ID)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidOSSubjsObjs_SubjsOwnObjsThenInSamePartition(subjs, objs, id_mappings, globals)

    requires WSM_IsUSBPDevID(subjs, usbpdev_id)

    ensures forall id :: id in subjs.usbpdevs[usbpdev_id].fd_ids
                ==> id in objs.usbpdev_fds
    ensures forall id :: id in subjs.usbpdevs[usbpdev_id].do_ids
                ==> id in objs.usbpdev_dos
        // Properties needed by the following properties
    ensures forall id :: id in subjs.usbpdevs[usbpdev_id].fd_ids
                ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WSM_SubjPID(subjs, objs, id_mappings, globals, usbpdev_id.sid)
    ensures forall id :: id in subjs.usbpdevs[usbpdev_id].do_ids
                ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WSM_SubjPID(subjs, objs, id_mappings, globals, usbpdev_id.sid)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    forall id | id in subjs.usbpdevs[usbpdev_id].fd_ids
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) == WSM_SubjPID(subjs, objs, id_mappings, globals, usbpdev_id.sid)
    {
        // Dafny can automatically prove it
    }
}

// Lemma: EEHCIs' objects must be in WSM_AllTD/FD/DOIDs
lemma Lemma_eEHCIs_ProveObjsAreInSystem(s:state, dev_id:Dev_ID)
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires dev_id in s.subjects.eehcis

    ensures forall id :: id in s.subjects.eehcis[dev_id].td_ids
                ==> id in WSM_AllTDIDs(s.objects)
    ensures forall id :: id in s.subjects.eehcis[dev_id].fd_ids
                ==> id in WSM_AllFDIDs(s.objects)
    ensures forall id :: id in s.subjects.eehcis[dev_id].do_ids
                ==> id in WSM_AllDOIDs(s.objects)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_eEHCIs();

    forall id | id in s.subjects.eehcis[dev_id].td_ids
        ensures id in WSM_AllTDIDs(s.objects)
    {
        assert id in OwnedTDs_eEHCI_ExcludeHCodedTD(s.subjects, dev_id) || id == s.subjects.eehcis[dev_id].hcoded_td_id;

        if(id in OwnedTDs_eEHCI_ExcludeHCodedTD(s.subjects, dev_id))
        {
            assert id in s.objects.eehci_other_tds;
            assert id in WSM_AllTDIDs(s.objects);
        }
        else
        {
            assert id in WSM_AllTDIDs(s.objects);
        }
    }
}