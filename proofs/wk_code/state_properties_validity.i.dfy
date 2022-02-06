include "state_properties_validity.s.dfy"
include "utils/model/utils_subjs_objs.i.dfy"
include "drv/public/wimpdrv_lemmas.i.dfy"

// [ID Mapping] Axiom (well known): In each slot of <g_usbtd_map_mem>, if the ID is not USBTD_ID_INVALID, then its 
// mapped TD/FD/DO must be in the system.
// [NOTE] This axiom makes sense, because there always exists an initial state knowing the maximum USBTD ID counter a  
// trace would end up with.
lemma {:axiom} Lemma_USBTD_AllIDsBelowCounterMapToExistingTDFDDOInSystem(
    objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap
)
    requires WK_ValidGlobalVars_Decls(globals)
    requires forall slot :: usbtd_map_valid_slot_id(slot)
                ==> (usbtd_map_get_idword(globals, slot) <= usbtd_id_counter_read(globals) ||
                    usbtd_map_get_idword(globals, slot) == USBTD_ID_INVALID)
        // Requirement: Necessary properties from <WK_USBTD_Map_ValidGlobalVarValues>
    requires (forall e:word :: e != USBTD_ID_INVALID
                <==> e in id_mappings.usbtd_to_td) &&
            (forall e:word :: e != USBTD_ID_INVALID
                <==> e in id_mappings.usbtd_to_fd) &&
            (forall e:word :: e != USBTD_ID_INVALID
                <==> e in id_mappings.usbtd_to_do)
        // Requirement: Necessary properties from <WK_ValidIDMappings>

    ensures forall slot :: usbtd_map_valid_slot_id(slot) &&
                    usbtd_map_get_idword(globals, slot) != USBTD_ID_INVALID
                ==> (
                        var usbtd_idword := usbtd_map_get_idword(globals, slot);
                        var usbtd_td_id:TD_ID := id_mappings.usbtd_to_td[usbtd_idword];
                        var usbtd_fd_id:FD_ID := id_mappings.usbtd_to_fd[usbtd_idword];
                        var usbtd_do_id:DO_ID := id_mappings.usbtd_to_do[usbtd_idword];

                        usbtd_td_id in objs.usbtd_tds &&
                        usbtd_fd_id in objs.usbtd_fds &&
                        usbtd_do_id in objs.usbtd_dos
                    )
        // Property: In each slot of <g_usbtd_map_mem>, if the ID is not USBTD_ID_INVALID, then its mapped TD/FD/DO must 
        // be in the system




/*********************** Properties Derived From SIs (These predicates are not SIs) ********************/
// State validity properties related to active USB TDs in global variables
predicate {:opaque} WK_ValidGlobalVarValues_ActiveUSBTDs(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap
)
    requires WK_ValidGlobalVars_Decls(globals)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires WK_USBTD_Map_ValidGlobalVarValues_IDWords(globals)
{
    reveal WK_ValidIDMappings();
    assert WK_USBTD_Map_ValidGlobalVarValues_IDWords(globals);

    // If a USB TD is active, then its mapped TD, FD and DO must exists in the system
    (forall slot :: usbtd_map_valid_slot_id(slot) &&
            usbtd_map_get_pid(globals, slot) != WS_PartitionID(PID_INVALID)
        ==> (
                var usbtd_idword := usbtd_map_get_idword(globals, slot);
                var usbtd_td_id:TD_ID := id_mappings.usbtd_to_td[usbtd_idword];
                var usbtd_fd_id:FD_ID := id_mappings.usbtd_to_fd[usbtd_idword];
                var usbtd_do_id:DO_ID := id_mappings.usbtd_to_do[usbtd_idword];

                usbtd_td_id in objs.usbtd_tds &&
                usbtd_fd_id in objs.usbtd_fds &&
                usbtd_do_id in objs.usbtd_dos
            )
    )
}

// Predicate: Only OS objects and USBPDevs' objects can be active in the OS partition
predicate {:opaque} WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
{
    // eEHCIs' objects cannot be in the OS partition
    (forall id :: id in objs.eehci_hcoded_tds
        ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
    (forall id :: id in objs.eehci_other_tds
        ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
    (forall id :: id in objs.eehci_fds
        ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
    (forall id :: id in objs.eehci_dos
        ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&

    // Wimp drivers' objects cannot be in the OS partition
    (forall id :: id in objs.wimpdrv_dos
        ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&

    // External USB TDs cannot be in the OS partition
    (forall id :: id in objs.usbtd_tds
        ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
    (forall id :: id in objs.usbtd_fds
        ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&
    (forall id :: id in objs.usbtd_dos
        ==> WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    ) &&

    (true)
}




/*********************** Lemmas ********************/
lemma Lemma_ValidState_ProveWK_ValidObjs_ObjIDs(s:state)
    requires ValidState(s)

    ensures WK_ValidObjs_ObjIDs(s.objects)
{
    reveal WK_ValidObjs();
}

lemma Lemma_ValidState_ImpliesWK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap
)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)

    ensures WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(subjs, objs, id_mappings, globals);
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();

    reveal WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition();

    // Prove: External USB TDs cannot be in the OS partition
    assert (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_pid(globals, i));
    assert WS_PartitionID(PID_RESERVED_OS_PARTITION) !in pids_parse_g_wimp_pids(globals);

    forall id | id in objs.usbtd_tds
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    {
        var pid := WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid);
        assert pid == ObjPID_USBTDMappedObjs(subjs, objs, id_mappings, globals, id.oid);

        var idword := USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, id.oid);

        if(usbtd_idword_in_record(globals, idword))
        {
            var usbtd_slot := usbtd_get_slot_by_idword(globals, idword);
            assert pid == usbtd_map_get_pid(globals, usbtd_slot);
            assert usbtd_slot_valid_pid(globals, usbtd_slot);
            assert pid == WS_PartitionID(PID_INVALID) || pid in pids_parse_g_wimp_pids(globals);
            assert pid != WS_PartitionID(PID_RESERVED_OS_PARTITION);
        }
        else
        {
            assert pid == WS_PartitionID(PID_INVALID);
        }
    }

    forall id | id in objs.usbtd_fds
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    {
        var pid := WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid);
        assert pid == ObjPID_USBTDMappedObjs(subjs, objs, id_mappings, globals, id.oid);

        var idword := USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, id.oid);

        if(usbtd_idword_in_record(globals, idword))
        {
            var usbtd_slot := usbtd_get_slot_by_idword(globals, idword);
            assert pid == usbtd_map_get_pid(globals, usbtd_slot);
            assert usbtd_slot_valid_pid(globals, usbtd_slot);
            assert pid == WS_PartitionID(PID_INVALID) || pid in pids_parse_g_wimp_pids(globals);
            assert pid != WS_PartitionID(PID_RESERVED_OS_PARTITION);
        }
        else
        {
            assert pid == WS_PartitionID(PID_INVALID);
        }
    }

    forall id | id in objs.usbtd_dos
        ensures WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid) != WS_PartitionID(PID_RESERVED_OS_PARTITION)
    {
        var pid := WSM_ObjPID(subjs, objs, id_mappings, globals, id.oid);
        assert pid == ObjPID_USBTDMappedObjs(subjs, objs, id_mappings, globals, id.oid);

        var idword := USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, id.oid);

        if(usbtd_idword_in_record(globals, idword))
        {
            var usbtd_slot := usbtd_get_slot_by_idword(globals, idword);
            assert pid == usbtd_map_get_pid(globals, usbtd_slot);
            assert usbtd_slot_valid_pid(globals, usbtd_slot);
            assert pid == WS_PartitionID(PID_INVALID) || pid in pids_parse_g_wimp_pids(globals);
            assert pid != WS_PartitionID(PID_RESERVED_OS_PARTITION);
        }
        else
        {
            assert pid == WS_PartitionID(PID_INVALID);
        }
    }
}

lemma Lemma_ValidState_ImpliesWK_ValidGlobalVarValues_ActiveUSBTDs(
    subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap
)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)

    requires WK_ValidGlobalVars_Decls(globals)
    requires forall slot :: usbtd_map_valid_slot_id(slot)
                ==> (usbtd_map_get_idword(globals, slot) <= usbtd_id_counter_read(globals) ||
                    usbtd_map_get_idword(globals, slot) == USBTD_ID_INVALID)
    requires WK_USBTD_Map_ValidGlobalVarValues_IDWords(globals)
        // Requirement: Necessary properties from <WK_USBTD_Map_ValidGlobalVarValues>

    ensures WK_ValidGlobalVarValues_ActiveUSBTDs(subjs, objs, id_mappings, globals);
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidIDMappings();

    reveal WK_ValidGlobalVarValues_ActiveUSBTDs();

    // Prove pre-condition of Lemma_USBTD_AllIDsBelowCounterMapToExistingTDFDDOInSystem
    forall slot:uint32 | usbtd_map_valid_slot_id(slot)
        ensures usbtd_map_get_idword(globals, slot) <= usbtd_id_counter_read(globals) ||
                usbtd_map_get_idword(globals, slot) == USBTD_ID_INVALID
    {
        assert 0 <= slot < USB_TD_ENTRY_NUM;
        assert (forall i :: 0 <= i < USB_TD_ENTRY_NUM ==> usbtd_slot_valid_id(globals, i));
        assert usbtd_slot_valid_id(globals, slot);
        //assert usbtd_map_get_idword(globals, slot) <= usbtd_id_counter_read(globals);
    }

    Lemma_USBTD_AllIDsBelowCounterMapToExistingTDFDDOInSystem(objs, id_mappings, globals);
}

// Lemma: On <s.object> modification, if ObjIDs are unchanged and hardcoded TDs are unchanged, then WK_ValidObjs_HCodedTDs holds
lemma Lemma_ValidObjs_OnObjectModification_IfObjIDsAreSame_HCodedTDs(s:state, s':state)
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidObjs_ObjInSubjsMustBeInState(s'.subjects, s'.objects)

    requires s.subjects == s'.subjects
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires s.objects.eehci_hcoded_tds == s'.objects.eehci_hcoded_tds
    requires s.objects.usbpdev_tds == s'.objects.usbpdev_tds
    requires forall dev_id :: dev_id in s.subjects.os_devs
                ==> s.subjects.os_devs[dev_id].hcoded_td_id in s.objects.os_tds
    requires forall dev_id :: dev_id in s.subjects.os_devs
                ==> s.objects.os_tds[s.subjects.os_devs[dev_id].hcoded_td_id] == s'.objects.os_tds[s.subjects.os_devs[dev_id].hcoded_td_id]
        // Requirement: Hardcoded TDs are unchanged      

    ensures forall dev_id :: dev_id in s'.subjects.os_devs
                ==> s'.subjects.os_devs[dev_id].hcoded_td_id in s'.subjects.os_devs[dev_id].td_ids
    ensures WK_ValidObjs_HCodedTDs(s'.subjects, s'.objects)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidObjs_HCodedTDs();

    Lemma_OSDevs_HCodedTDsMapToUnchangedVals(s, s');
}

// Lemma: If subjects are not changed and only WimpDrv DOs' contents in objects are changed, then WK_ValidSubjs and
// WK_ValidObjs hold
lemma Lemma_WK_ValidSubjsObjs_HoldIfOnlyWimpDrvDOValsAreChangedInObjs(s:state, r:state)
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires s.subjects == r.subjects
    requires s.id_mappings == r.id_mappings
    requires s.objects.os_tds == r.objects.os_tds &&
            s.objects.os_fds == r.objects.os_fds &&
            s.objects.os_dos == r.objects.os_dos &&
            s.objects.eehci_hcoded_tds == r.objects.eehci_hcoded_tds &&
            s.objects.eehci_other_tds == r.objects.eehci_other_tds &&
            s.objects.eehci_fds == r.objects.eehci_fds &&
            s.objects.eehci_dos == r.objects.eehci_dos &&
            s.objects.usbpdev_tds == r.objects.usbpdev_tds &&
            s.objects.usbpdev_fds == r.objects.usbpdev_fds &&
            s.objects.usbpdev_dos == r.objects.usbpdev_dos &&
            MapGetKeys(s.objects.wimpdrv_dos) == MapGetKeys(r.objects.wimpdrv_dos) &&
            s.objects.usbtd_tds == r.objects.usbtd_tds &&
            s.objects.usbtd_fds == r.objects.usbtd_fds &&
            s.objects.usbtd_dos == r.objects.usbtd_dos

    ensures WK_ValidSubjs(r.subjects, r.id_mappings)
    ensures WK_ValidObjs(r.subjects, r.objects) 
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_HCodedTDs();
    reveal WK_ValidObjs_InternalObjsOf_WimpSubjects();
    reveal WK_ValidObjs_eEHCIs();

    Lemma_ValidObjs_OnObjectModification_IfObjIDsAreSame_HCodedTDs(s, r);
}

// Lemma: On <s.object> modification, If ObjIDs are unchanged, then WK_ValidIDMappings holds
lemma Lemma_ValidIDMappings_OnObjectModification_IfObjIDsAreUnchanged(s:state, s':state)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)

    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged

    ensures WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
{
    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();
    reveal WK_ValidIDMappings_AdditonalPredicatesOfUSBTDObjs();
}

// Lemma: If subjects are not changed and only USBPDev FDs' and DOs' contents in objects are changed, then WK_ValidSubjs and
// WK_ValidObjs hold
lemma Lemma_WK_ValidSubjsObjs_HoldIfOnlyUSBPDevFDDOValsAreChangedInObjs(s:state, r:state)
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires s.subjects == r.subjects
    requires s.id_mappings == r.id_mappings
    requires s.objects.os_tds == r.objects.os_tds &&
            s.objects.os_fds == r.objects.os_fds &&
            s.objects.os_dos == r.objects.os_dos &&
            s.objects.eehci_hcoded_tds == r.objects.eehci_hcoded_tds &&
            s.objects.eehci_other_tds == r.objects.eehci_other_tds &&
            s.objects.eehci_fds == r.objects.eehci_fds &&
            s.objects.eehci_dos == r.objects.eehci_dos &&
            s.objects.usbpdev_tds == r.objects.usbpdev_tds &&
            MapGetKeys(s.objects.usbpdev_fds) == MapGetKeys(r.objects.usbpdev_fds) &&
            MapGetKeys(s.objects.usbpdev_dos) == MapGetKeys(r.objects.usbpdev_dos) &&
            s.objects.wimpdrv_dos == r.objects.wimpdrv_dos &&
            s.objects.usbtd_tds == r.objects.usbtd_tds &&
            s.objects.usbtd_fds == r.objects.usbtd_fds &&
            s.objects.usbtd_dos == r.objects.usbtd_dos

    ensures WK_ValidSubjs(r.subjects, r.id_mappings)
    ensures WK_ValidObjs(r.subjects, r.objects) 
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_HCodedTDs();
    reveal WK_ValidObjs_InternalObjsOf_WimpSubjects();
    reveal WK_ValidObjs_eEHCIs();

    Lemma_MapSameKeys(s.objects.usbpdev_fds, r.objects.usbpdev_fds);
    Lemma_MapSameKeys(s.objects.usbpdev_dos, r.objects.usbpdev_dos);

    Lemma_ValidObjs_OnObjectModification_IfObjIDsAreSame_HCodedTDs(s, r);
}

// Lemma: If subjects are not changed and only inactive objects' values in objects are changed, then WK_ValidSubjs and
// WK_ValidObjs hold
lemma Lemma_WK_ValidSubjsObjs_HoldIfOnlyInactiveObjsValsAreChanged(s:state, r:state)
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires s.subjects == r.subjects
    requires s.id_mappings == r.id_mappings
    requires s.objects.os_tds == r.objects.os_tds &&
            s.objects.os_fds == r.objects.os_fds &&
            s.objects.os_dos == r.objects.os_dos &&
            s.objects.eehci_hcoded_tds == r.objects.eehci_hcoded_tds &&
            s.objects.eehci_other_tds == r.objects.eehci_other_tds &&
            s.objects.eehci_fds == r.objects.eehci_fds &&
            s.objects.eehci_dos == r.objects.eehci_dos &&
            s.objects.usbpdev_tds == r.objects.usbpdev_tds &&
            s.objects.usbpdev_fds == r.objects.usbpdev_fds &&
            s.objects.usbpdev_dos == r.objects.usbpdev_dos &&
            s.objects.wimpdrv_dos == r.objects.wimpdrv_dos &&
            s.objects.usbtd_tds == r.objects.usbtd_tds &&
            s.objects.usbtd_fds == r.objects.usbtd_fds &&
            s.objects.usbtd_dos == r.objects.usbtd_dos

    ensures WK_ValidSubjs(r.subjects, r.id_mappings)
    ensures WK_ValidObjs(r.subjects, r.objects) 
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_HCodedTDs();
    reveal WK_ValidObjs_InternalObjsOf_WimpSubjects();
    reveal WK_ValidObjs_eEHCIs();
}

// Lemma: On <s.wk_mstate> modification, If <g_wimpdrvs_info> and <g_eehci_mem_pbase> are unchanged, and OS objects have 
// unchanged PID, then WK_ValidObjAddrs_WimpDrv_DOPAddrs holds
lemma Lemma_WK_ValidObjAddrs_WimpDrv_DOPAddrs_OnWKMStateModification_IfWimpDrvsInfoEEHCIIMemPBaseAreUnchangedAndOSObjsHaveUnchangedPID(s:state, s':state)
    requires ValidState(s)

    requires WK_ValidMState(s'.wk_mstate)
    requires WK_ValidSubjs(s'.subjects, s'.id_mappings)
    requires WK_ValidIDMappings(s'.subjects, s'.objects, s'.id_mappings)
    requires WK_ValidObjs(s'.subjects, s'.objects) 

    requires global_read_fullval(wkm_get_globals(s.wk_mstate), G_WimpDrvs_Info()) == global_read_fullval(wkm_get_globals(s'.wk_mstate), G_WimpDrvs_Info())
    requires eehci_mem_pbase(wkm_get_globals(s.wk_mstate)) == eehci_mem_pbase(wkm_get_globals(s'.wk_mstate))
        // Requirement: <g_wimpdrvs_info> and <g_eehci_mem_pbase> are unchanged
    requires s.subjects == s'.subjects
    requires s.id_mappings == s'.id_mappings
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged
    requires forall id :: WSM_IsOSObj(s.objects, id)
                ==> WSM_ObjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), id) ==
                    WSM_ObjPID(s'.subjects, s'.objects, s'.id_mappings, wkm_get_globals(s'.wk_mstate), id)
        // Requirement: OS objects have unchanged PID

    ensures WK_ValidObjAddrs_WimpDrv_DOPAddrs(s'.subjects, s'.objects, s'.id_mappings, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidObjAddrs_WimpDrv_DOPAddrs();
}

// Lemma: On <s.wk_mstate> or <s.subjects> modification, If <g_usbtd_map_mem> is unchanged, then 
// WK_ValidGlobalVarValues_USBPDevs holds
lemma Lemma_WK_ValidGlobalVarValues_USBPDevs_OnWKMStateSubjectsModification_IfWimpUSBPDevInfoAndUSBPDevListAreUnchanged(s:state, s':state)
    requires ValidState(s)

    requires WK_ValidMState(s'.wk_mstate)

    requires global_read_fullval(wkm_get_globals(s.wk_mstate), G_WimpUSBPDev_Info()) == global_read_fullval(wkm_get_globals(s'.wk_mstate), G_WimpUSBPDev_Info())
    requires global_read_fullval(wkm_get_globals(s.wk_mstate), G_WimpUSBPDev_DevList()) == global_read_fullval(wkm_get_globals(s'.wk_mstate), G_WimpUSBPDev_DevList())
        // Requirement: <g_usbtd_map_mem> is unchanged
    requires s.id_mappings == s'.id_mappings
    requires s.subjects.usbpdevs == s'.subjects.usbpdevs
        // Requirement: <s.subjects.usbpdevs> are unchanged

    ensures WK_ValidGlobalVarValues_USBPDevs(s'.subjects, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidGlobalVarValues_USBPDevs();

    var globals' := wkm_get_globals(s'.wk_mstate);

    forall slot | usbpdev_valid_slot_id(slot) &&
            usbpdev_get_pid(globals', slot) != WS_PartitionID(PID_INVALID) &&
            usbpdev_get_updateflag(globals', slot) == WimpUSBPDev_Slot_UpdateFlag_Complete
        ensures (
                var usbpdev_addr_raw:uint64 := usbpdev_get_addr(globals', slot);
                var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);

                usbpdev_addr in usbpdevlist_get_all_non_empty_addrs(globals')
            )
    {
        var usbpdev_addr_raw:uint64 := usbpdev_get_addr(globals', slot);
        var usbpdev_addr:USBPDev_Addr := usb_parse_usbpdev_addr(usbpdev_addr_raw);
    }

    forall usbpdev_id:Dev_ID | WSM_IsUSBPDevID(s'.subjects, usbpdev_id)
        ensures (
                    s'.subjects.usbpdevs[usbpdev_id].active_in_os == true
                        ==> (forall i :: usbpdev_valid_slot_id(i)
                                    ==> usbpdev_get_pid(globals', i) == WS_PartitionID(PID_INVALID))
                )
    {
        assert WSM_IsUSBPDevID(s.subjects, usbpdev_id);
    }
}

// Lemma: On <s.wk_mstate> or <s.subjects> modification, If <g_wimpdevs_devlist> is unchanged, then 
// WK_ValidGlobalVarValues_USBPDevList holds
lemma Lemma_WK_ValidGlobalVarValues_USBPDevList_OnWKMStateSubjectsModification_IfUSBPDevListIsUnchanged(s:state, s':state)
    requires ValidState(s)

    requires WK_ValidMState(s'.wk_mstate)

    requires global_read_fullval(wkm_get_globals(s.wk_mstate), G_WimpUSBPDev_DevList()) == global_read_fullval(wkm_get_globals(s'.wk_mstate), G_WimpUSBPDev_DevList())
        // Requirement: <g_usbtd_map_mem> is unchanged
    requires s.id_mappings == s'.id_mappings
    requires WSM_SubjIDsAreSame(s.subjects, s'.subjects)
        // Requirement: Subject IDs are unchanged

    ensures WK_ValidGlobalVarValues_USBPDevList(s'.subjects, s.id_mappings, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjsAddrs();
    reveal WK_SecureObjsAddrs_MemSeparation();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidGlobalVarValues_USBPDevList();
}

// Lemma: If only PIDs of OS's subjects and objects are changed, then WK_ValidSubjs and WK_ValidObjs hold
lemma Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsPIDsAreChanged(s:state, r:state)
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)

    requires MapGetKeys(s.subjects.os_drvs) == MapGetKeys(r.subjects.os_drvs)
    requires MapGetKeys(s.subjects.os_devs) == MapGetKeys(r.subjects.os_devs)
    requires s.subjects.wimp_drvs == r.subjects.wimp_drvs
    requires s.subjects.eehcis == r.subjects.eehcis
    requires MapGetKeys(s.subjects.usbpdevs) == MapGetKeys(r.subjects.usbpdevs)

    requires forall id :: id in s.subjects.os_drvs
                ==> (s.subjects.os_drvs[id].td_ids == r.subjects.os_drvs[id].td_ids &&
                     s.subjects.os_drvs[id].fd_ids == r.subjects.os_drvs[id].fd_ids &&
                     s.subjects.os_drvs[id].do_ids == r.subjects.os_drvs[id].do_ids)
    requires forall id :: id in s.subjects.os_devs
                ==> (s.subjects.os_devs[id].hcoded_td_id == r.subjects.os_devs[id].hcoded_td_id &&
                     s.subjects.os_devs[id].td_ids == r.subjects.os_devs[id].td_ids &&
                     s.subjects.os_devs[id].fd_ids == r.subjects.os_devs[id].fd_ids &&
                     s.subjects.os_devs[id].do_ids == r.subjects.os_devs[id].do_ids)
    requires forall id :: id in s.subjects.usbpdevs
                ==> (s.subjects.usbpdevs[id].hcoded_td_id == r.subjects.usbpdevs[id].hcoded_td_id &&
                     s.subjects.usbpdevs[id].fd_ids == r.subjects.usbpdevs[id].fd_ids &&
                     s.subjects.usbpdevs[id].do_ids == r.subjects.usbpdevs[id].do_ids)
        // Requirement: Objects ownerships in OS are unchanged

    requires s.id_mappings == r.id_mappings

    requires MapGetKeys(s.objects.os_tds) == MapGetKeys(r.objects.os_tds) &&
             MapGetKeys(s.objects.os_fds) == MapGetKeys(r.objects.os_fds) &&
             MapGetKeys(s.objects.os_dos) == MapGetKeys(r.objects.os_dos) &&
             s.objects.eehci_hcoded_tds == r.objects.eehci_hcoded_tds &&
            s.objects.eehci_other_tds == r.objects.eehci_other_tds &&
            s.objects.eehci_fds == r.objects.eehci_fds &&
            s.objects.eehci_dos == r.objects.eehci_dos &&
            s.objects.usbpdev_tds == r.objects.usbpdev_tds &&
            s.objects.usbpdev_fds == r.objects.usbpdev_fds &&
            s.objects.usbpdev_dos == r.objects.usbpdev_dos &&
            s.objects.wimpdrv_dos == r.objects.wimpdrv_dos &&
            s.objects.usbtd_tds == r.objects.usbtd_tds &&
            s.objects.usbtd_fds == r.objects.usbtd_fds &&
            s.objects.usbtd_dos == r.objects.usbtd_dos

    requires forall id :: id in s.subjects.os_devs
                ==> s.subjects.os_devs[id].hcoded_td_id in s.objects.os_tds
    requires forall id :: id in s.subjects.os_devs
                ==> s.objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val == r.objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val
        // Requirement: Values of Hardcoded TDs in OS devices are unmodified

    ensures WK_ValidSubjs(r.subjects, r.id_mappings)
    ensures WK_ValidObjs(r.subjects, r.objects)
    ensures WK_ValidIDMappings(r.subjects, r.objects, r.id_mappings)
{
    reveal WK_ValidObjs();

    Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsIDsAreUnchanged_Subjects(s, r);
    Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsPIDsAreChanged_Objects(s, r);
    Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsIDsAreUnchanged_IDMappings(s, r);
}

lemma Lemma_WK_ValidGlobalVars_Vals_HoldForUnchangedGlobals(old_wkm:WK_MState, new_wkm:WK_MState)
    requires WK_ValidGlobalState(wkm_get_globals(old_wkm))
    requires wkm_get_globals(old_wkm) == wkm_get_globals(new_wkm)

    ensures WK_ValidGlobalState(wkm_get_globals(new_wkm)) 
{
    Lemma_WK_WimpDrvs_ValidGlobalVarValues_HoldForUnchangedGlobals(old_wkm, new_wkm);
    Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGVarUnchanged(wkm_get_globals(old_wkm), wkm_get_globals(new_wkm));
}

// Lemma: Properties of WK_ValidObjs
lemma Lemma_WK_ValidObjs_Properties(subjs:WSM_Subjects, objs:WSM_Objects)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs(subjs, objs)

    ensures forall dev_id :: dev_id in subjs.os_devs
                ==> subjs.os_devs[dev_id].hcoded_td_id in objs.os_tds
    ensures forall dev_id :: dev_id in subjs.os_devs
                ==> subjs.os_devs[dev_id].hcoded_td_id in subjs.os_devs[dev_id].td_ids
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
}

// Lemma: On <s.object> modification, If ObjIDs are unchanged, then WK_ValidObjsAddrs holds
lemma Lemma_ValidObjsAddrs_OnObjectModification_IfObjIDsAreUnchanged(s:state, s':state)
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s.wk_mstate))
    requires WK_ValidGlobalVars_Decls(wkm_get_globals(s'.wk_mstate))
    requires WK_ValidObjsAddrs(s.objects, s.objs_addrs, wkm_get_globals(s.wk_mstate))

    requires wkm_get_globals(s.wk_mstate) == wkm_get_globals(s'.wk_mstate)
    requires s.objs_addrs == s'.objs_addrs
    requires WSM_ObjIDsAreSame(s.objects, s'.objects)
        // Requirement: Object IDs are unchanged

    ensures WK_ValidObjsAddrs(s'.objects, s'.objs_addrs, wkm_get_globals(s'.wk_mstate))
{
    reveal WK_ValidObjsAddrs();
}

lemma Lemma_WK_ValidState_DevsActivateCond_Property(s:state)
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)
    requires WK_ValidState_DevsActivateCond(s.subjects, s.objects, s.id_mappings, s.activate_conds, wkm_get_globals(s.wk_mstate)) 

    ensures forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
        // Requirement from <WK_ValidState_DevsActivateCond>
{
    reveal WK_ValidState_DevsActivateCond();
}




/*********************** Private Lemmas ********************/
// Lemma: If IDs of OS's subjects and objects are unchanged, then WK_ValidSubjs and WK_ValidObjs hold
lemma Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsIDsAreUnchanged_Subjects(s:state, r:state)
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)

    requires MapGetKeys(s.subjects.os_drvs) == MapGetKeys(r.subjects.os_drvs)
    requires MapGetKeys(s.subjects.os_devs) == MapGetKeys(r.subjects.os_devs)
    requires s.subjects.wimp_drvs == r.subjects.wimp_drvs
    requires s.subjects.eehcis == r.subjects.eehcis
    requires MapGetKeys(s.subjects.usbpdevs) == MapGetKeys(r.subjects.usbpdevs)

    requires s.id_mappings == r.id_mappings

    requires MapGetKeys(s.objects.os_tds) == MapGetKeys(r.objects.os_tds) &&
             MapGetKeys(s.objects.os_fds) == MapGetKeys(r.objects.os_fds) &&
             MapGetKeys(s.objects.os_dos) == MapGetKeys(r.objects.os_dos) &&
             s.objects.eehci_hcoded_tds == r.objects.eehci_hcoded_tds &&
            s.objects.eehci_other_tds == r.objects.eehci_other_tds &&
            s.objects.eehci_fds == r.objects.eehci_fds &&
            s.objects.eehci_dos == r.objects.eehci_dos &&
            s.objects.usbpdev_tds == r.objects.usbpdev_tds &&
            s.objects.usbpdev_fds == r.objects.usbpdev_fds &&
            s.objects.usbpdev_dos == r.objects.usbpdev_dos &&
            s.objects.wimpdrv_dos == r.objects.wimpdrv_dos &&
            s.objects.usbtd_tds == r.objects.usbtd_tds &&
            s.objects.usbtd_fds == r.objects.usbtd_fds &&
            s.objects.usbtd_dos == r.objects.usbtd_dos

    ensures WK_ValidSubjs(r.subjects, r.id_mappings)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_eEHCIs();
    reveal WK_ValidSubjs_SubjIDs();
}

// Lemma: If only PIDs of OS's subjects and objects are changed, then WK_ValidSubjs and WK_ValidObjs hold
lemma Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsPIDsAreChanged_Objects(s:state, r:state)
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidSubjs(r.subjects, r.id_mappings)

    requires MapGetKeys(s.subjects.os_drvs) == MapGetKeys(r.subjects.os_drvs)
    requires MapGetKeys(s.subjects.os_devs) == MapGetKeys(r.subjects.os_devs)
    requires s.subjects.wimp_drvs == r.subjects.wimp_drvs
    requires s.subjects.eehcis == r.subjects.eehcis
    requires MapGetKeys(s.subjects.usbpdevs) == MapGetKeys(r.subjects.usbpdevs)

    requires forall id :: id in s.subjects.os_drvs
                ==> (s.subjects.os_drvs[id].td_ids == r.subjects.os_drvs[id].td_ids &&
                     s.subjects.os_drvs[id].fd_ids == r.subjects.os_drvs[id].fd_ids &&
                     s.subjects.os_drvs[id].do_ids == r.subjects.os_drvs[id].do_ids)
    requires forall id :: id in s.subjects.os_devs
                ==> (s.subjects.os_devs[id].hcoded_td_id == r.subjects.os_devs[id].hcoded_td_id &&
                     s.subjects.os_devs[id].td_ids == r.subjects.os_devs[id].td_ids &&
                     s.subjects.os_devs[id].fd_ids == r.subjects.os_devs[id].fd_ids &&
                     s.subjects.os_devs[id].do_ids == r.subjects.os_devs[id].do_ids)
    requires forall id :: id in s.subjects.usbpdevs
                ==> (s.subjects.usbpdevs[id].hcoded_td_id == r.subjects.usbpdevs[id].hcoded_td_id &&
                     s.subjects.usbpdevs[id].fd_ids == r.subjects.usbpdevs[id].fd_ids &&
                     s.subjects.usbpdevs[id].do_ids == r.subjects.usbpdevs[id].do_ids)
        // Requirement: Objects ownerships in OS are unchanged

    requires s.id_mappings == r.id_mappings

    requires MapGetKeys(s.objects.os_tds) == MapGetKeys(r.objects.os_tds) &&
             MapGetKeys(s.objects.os_fds) == MapGetKeys(r.objects.os_fds) &&
             MapGetKeys(s.objects.os_dos) == MapGetKeys(r.objects.os_dos) &&
             s.objects.eehci_hcoded_tds == r.objects.eehci_hcoded_tds &&
            s.objects.eehci_other_tds == r.objects.eehci_other_tds &&
            s.objects.eehci_fds == r.objects.eehci_fds &&
            s.objects.eehci_dos == r.objects.eehci_dos &&
            s.objects.usbpdev_tds == r.objects.usbpdev_tds &&
            s.objects.usbpdev_fds == r.objects.usbpdev_fds &&
            s.objects.usbpdev_dos == r.objects.usbpdev_dos &&
            s.objects.wimpdrv_dos == r.objects.wimpdrv_dos &&
            s.objects.usbtd_tds == r.objects.usbtd_tds &&
            s.objects.usbtd_fds == r.objects.usbtd_fds &&
            s.objects.usbtd_dos == r.objects.usbtd_dos

    requires forall id :: id in s.subjects.os_devs
                ==> s.subjects.os_devs[id].hcoded_td_id in s.objects.os_tds
    requires forall id :: id in s.subjects.os_devs
                ==> s.objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val == r.objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val
        // Requirement: Values of Hardcoded TDs in OS devices are unmodified

    ensures WK_ValidObjs(r.subjects, r.objects)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidObjs_HCodedTDs();
    reveal WK_ValidObjs_InternalObjsOf_WimpSubjects();
    reveal WK_ValidObjs_eEHCIs();

    assert WK_ValidObjs_ObjIDs(r.objects);

    forall id | id in r.subjects.os_devs
        ensures r.subjects.os_devs[id].hcoded_td_id in r.objects.os_tds
    {
        assert s.subjects.os_devs[id].hcoded_td_id == r.subjects.os_devs[id].hcoded_td_id;
    }

    forall o_id, s_id1, s_id2 | 
        s_id1 in WSM_AllSubjsIDs(r.subjects) && s_id2 in WSM_AllSubjsIDs(r.subjects) && 
        WSM_DoOwnObj(r.subjects, s_id1, o_id) && WSM_DoOwnObj(r.subjects, s_id2, o_id)
        ensures s_id1 == s_id2
    {
        assert WSM_AllSubjsIDs(s.subjects) == WSM_AllSubjsIDs(r.subjects);
        assert WSM_DoOwnObj(s.subjects, s_id1, o_id) == WSM_DoOwnObj(r.subjects, s_id1, o_id);
        assert WSM_DoOwnObj(s.subjects, s_id2, o_id) == WSM_DoOwnObj(r.subjects, s_id2, o_id);
    }

    assert WK_ValidObjs_ObjInSubjsMustBeInState(r.subjects, r.objects);
    Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsPIDsAreChanged_Objects_HCodedTDs(s, r);
    assert WK_ValidObjs_HCodedTDs(r.subjects, r.objects);
    assert WK_ValidObjs_InternalObjsOf_WimpSubjects(r.subjects, r.objects);
    assert WK_ValidObjs_eEHCIs(r.subjects, r.objects);
}

// Lemma: If only PIDs of OS's subjects and objects are changed, then WK_ValidIDMappings hold
lemma Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsIDsAreUnchanged_IDMappings(s:state, r:state)
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidIDMappings(s.subjects, s.objects, s.id_mappings)

    requires MapGetKeys(s.subjects.os_drvs) == MapGetKeys(r.subjects.os_drvs)
    requires MapGetKeys(s.subjects.os_devs) == MapGetKeys(r.subjects.os_devs)
    requires s.subjects.wimp_drvs == r.subjects.wimp_drvs
    requires s.subjects.eehcis == r.subjects.eehcis
    requires MapGetKeys(s.subjects.usbpdevs) == MapGetKeys(r.subjects.usbpdevs)

    requires s.id_mappings == r.id_mappings

    requires MapGetKeys(s.objects.os_tds) == MapGetKeys(r.objects.os_tds) &&
             MapGetKeys(s.objects.os_fds) == MapGetKeys(r.objects.os_fds) &&
             MapGetKeys(s.objects.os_dos) == MapGetKeys(r.objects.os_dos) &&
             s.objects.eehci_hcoded_tds == r.objects.eehci_hcoded_tds &&
            s.objects.eehci_other_tds == r.objects.eehci_other_tds &&
            s.objects.eehci_fds == r.objects.eehci_fds &&
            s.objects.eehci_dos == r.objects.eehci_dos &&
            s.objects.usbpdev_tds == r.objects.usbpdev_tds &&
            s.objects.usbpdev_fds == r.objects.usbpdev_fds &&
            s.objects.usbpdev_dos == r.objects.usbpdev_dos &&
            s.objects.wimpdrv_dos == r.objects.wimpdrv_dos &&
            s.objects.usbtd_tds == r.objects.usbtd_tds &&
            s.objects.usbtd_fds == r.objects.usbtd_fds &&
            s.objects.usbtd_dos == r.objects.usbtd_dos

    ensures WK_ValidIDMappings(r.subjects, r.objects, r.id_mappings)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_eEHCIs();
    reveal WK_ValidSubjs_SubjIDs();

    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_UniqueIDs();

    assert WK_ValidIDMappings_UniqueIDs(r.subjects, r.objects, r.id_mappings);
}

// Lemma: If only PIDs of OS's subjects and objects are changed, then WK_ValidSubjs and WK_ValidObjs hold
lemma Lemma_WK_ValidSubjsObjs_HoldIfOSSubjsObjsPIDsAreChanged_Objects_HCodedTDs(s:state, r:state)
    requires WK_ValidSubjs(s.subjects, s.id_mappings)
    requires WK_ValidObjs(s.subjects, s.objects)
    requires WK_ValidSubjs_SubjIDs(r.subjects)
    requires WK_ValidObjs_ObjInSubjsMustBeInState(r.subjects, r.objects)

    requires MapGetKeys(s.subjects.os_drvs) == MapGetKeys(r.subjects.os_drvs)
    requires MapGetKeys(s.subjects.os_devs) == MapGetKeys(r.subjects.os_devs)
    requires s.subjects.wimp_drvs == r.subjects.wimp_drvs
    requires s.subjects.eehcis == r.subjects.eehcis
    requires MapGetKeys(s.subjects.usbpdevs) == MapGetKeys(r.subjects.usbpdevs)

    requires forall id :: id in s.subjects.os_drvs
                ==> (s.subjects.os_drvs[id].td_ids == r.subjects.os_drvs[id].td_ids &&
                     s.subjects.os_drvs[id].fd_ids == r.subjects.os_drvs[id].fd_ids &&
                     s.subjects.os_drvs[id].do_ids == r.subjects.os_drvs[id].do_ids)
    requires forall id :: id in s.subjects.os_devs
                ==> (s.subjects.os_devs[id].hcoded_td_id == r.subjects.os_devs[id].hcoded_td_id &&
                     s.subjects.os_devs[id].td_ids == r.subjects.os_devs[id].td_ids &&
                     s.subjects.os_devs[id].fd_ids == r.subjects.os_devs[id].fd_ids &&
                     s.subjects.os_devs[id].do_ids == r.subjects.os_devs[id].do_ids)
    requires forall id :: id in s.subjects.usbpdevs
                ==> (s.subjects.usbpdevs[id].hcoded_td_id == r.subjects.usbpdevs[id].hcoded_td_id &&
                     s.subjects.usbpdevs[id].fd_ids == r.subjects.usbpdevs[id].fd_ids &&
                     s.subjects.usbpdevs[id].do_ids == r.subjects.usbpdevs[id].do_ids)
        // Requirement: Objects ownerships in OS are unchanged

    requires s.id_mappings == r.id_mappings

    requires MapGetKeys(s.objects.os_tds) == MapGetKeys(r.objects.os_tds) &&
             MapGetKeys(s.objects.os_fds) == MapGetKeys(r.objects.os_fds) &&
             MapGetKeys(s.objects.os_dos) == MapGetKeys(r.objects.os_dos) &&
             s.objects.eehci_hcoded_tds == r.objects.eehci_hcoded_tds &&
            s.objects.eehci_other_tds == r.objects.eehci_other_tds &&
            s.objects.eehci_fds == r.objects.eehci_fds &&
            s.objects.eehci_dos == r.objects.eehci_dos &&
            s.objects.usbpdev_tds == r.objects.usbpdev_tds &&
            s.objects.usbpdev_fds == r.objects.usbpdev_fds &&
            s.objects.usbpdev_dos == r.objects.usbpdev_dos &&
            s.objects.wimpdrv_dos == r.objects.wimpdrv_dos &&
            s.objects.usbtd_tds == r.objects.usbtd_tds &&
            s.objects.usbtd_fds == r.objects.usbtd_fds &&
            s.objects.usbtd_dos == r.objects.usbtd_dos

    requires forall id :: id in s.subjects.os_devs
                ==> s.subjects.os_devs[id].hcoded_td_id in s.objects.os_tds
    requires forall id :: id in s.subjects.os_devs
                ==> s.objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val == r.objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val
        // Requirement: Values of Hardcoded TDs in OS devices are unmodified

    ensures forall dev_id :: dev_id in r.subjects.os_devs
                ==> r.subjects.os_devs[dev_id].hcoded_td_id in r.subjects.os_devs[dev_id].td_ids
    ensures WK_ValidObjs_HCodedTDs(r.subjects, r.objects)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    reveal WK_ValidObjs_HCodedTDs();

    // Prove WSM_BuildMap_DevsToHCodedTDVals_OSDevs(s.subjects, s.objects) == WSM_BuildMap_DevsToHCodedTDVals_OSDevs(r.subjects, r.objects)
    Lemma_OSDevs_HCodedTDsMapToUnchangedVals(s, r);
    assert WSM_BuildMap_DevsToHCodedTDVals_OSDevs(s.subjects, s.objects) == WSM_BuildMap_DevsToHCodedTDVals_OSDevs(r.subjects, r.objects);

    assert WSM_BuildMap_DevsToHCodedTDVals_USBPDevs(s.subjects, s.objects) == WSM_BuildMap_DevsToHCodedTDVals_USBPDevs(r.subjects, r.objects);
    assert WSM_BuildMap_DevsToHCodedTDVals_EEHCIs(s.subjects, s.objects) == WSM_BuildMap_DevsToHCodedTDVals_EEHCIs(r.subjects, r.objects);
    assert WSM_BuildMap_DevsToHCodedTDVals(s.subjects, s.objects) == WSM_BuildMap_DevsToHCodedTDVals(r.subjects, r.objects);

    var subjs := s.subjects;
    var hcoded_tds := WSM_BuildMap_DevsToHCodedTDVals(r.subjects, r.objects);
    var subjs' := r.subjects;

    forall dev_id | dev_id in WSM_AllDevIDs(subjs')
        ensures (forall td_id :: td_id in HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds
            ==> HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds[td_id].amodes != {R,W})
    {
        // Dafny can automatically prove this lemma
    }

    forall dev_id, td_id | dev_id in WSM_AllDevIDs(subjs') &&
                td_id in HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds
        ensures td_id !in WSM_AllHCodedTDIDs(subjs')
    {
        assert td_id !in WSM_AllHCodedTDIDs(subjs);
    }

    forall dev_id | dev_id in WSM_AllDevIDs(subjs')
        ensures (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds) <= 
                WSM_OwnedTDs(subjs', dev_id.sid)) &&
            (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_fds) <= 
                WSM_OwnedFDs(subjs', dev_id.sid)) &&
            (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_dos) <= 
                WSM_OwnedDOs(subjs', dev_id.sid))
    {
        assert WSM_OwnedTDs(subjs, dev_id.sid) == WSM_OwnedTDs(subjs', dev_id.sid);
        assert WSM_OwnedFDs(subjs, dev_id.sid) == WSM_OwnedFDs(subjs', dev_id.sid);
        assert WSM_OwnedDOs(subjs, dev_id.sid) == WSM_OwnedDOs(subjs', dev_id.sid);
    }
}