include "../../proof/state_map_any_state.s.dfy"
include "utils_subjs_valid_state.s.dfy"

/*********************** Axioms ********************/
// [State/Ops Mapping] Axiom (well known): Given a state s, the driver issuing the read access (the driver has the DO), and the accessing physical memory range  
// this function returns the content of the memory region
// [NOTE] This function must exist, because states stores wimp drivers' DOs' contents in <s.objects.wimpdrv_dos>
function method {:axiom} wimpdrv_read_do_get_do_val(s:state, drv_id_word:word, paddr_start:paddr, paddr_end:uint) : string
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires wimpdrv_idword_in_record(wkm_get_globals(s.wk_mstate), drv_id_word)
    requires drv_id_word != WimpDrv_ID_RESERVED_EMPTY
    requires var globals := wkm_get_globals(s.wk_mstate);
             var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);
             wimpdrv_do_get_paddr_base(globals, drv_slot) <= paddr_start < paddr_end <= wimpdrv_do_get_paddr_end(globals, drv_slot)
        // Requirement: The accessing physical memory must be inside the physical memory range of the wimp driver's DO

// [State/Ops Mapping] Axiom (well known): Given a state s, the driver issuing the write access (the driver has the DO), and the updating physical memory range  
// and new content, this function returns the new value of the entire DO
// [NOTE] This function must exist, because states stores wimp drivers' DOs' contents in <s.objects.wimpdrv_dos>
function method {:axiom} wimpdrv_write_do_get_do_val(s:state, drv_id_word:word, paddr_start:paddr, paddr_end:uint, new_val:string) : DO_Val
    requires WK_ValidGlobalState(wkm_get_globals(s.wk_mstate))
    requires wimpdrv_idword_in_record(wkm_get_globals(s.wk_mstate), drv_id_word)
    requires drv_id_word != WimpDrv_ID_RESERVED_EMPTY
    requires var globals := wkm_get_globals(s.wk_mstate);
             var drv_slot := wimpdrv_get_slot_by_idword(globals, drv_id_word);
             wimpdrv_do_get_paddr_base(globals, drv_slot) <= paddr_start < paddr_end <= wimpdrv_do_get_paddr_end(globals, drv_slot)
        // Requirement: The accessing physical memory must be inside the physical memory range of the wimp driver's DO

// [HW] Axiom (well known): All possible values of the given FD/DO <o_id> owned by the USBPDev <dev_id> is a finite set
function method {:axiom} usbpdev_string_range_for_fds_dos(subjs:WSM_Subjects, dev_id:Dev_ID, o_id:Object_ID) : set<string>
    requires WSM_IsUSBPDevID(subjs, dev_id)

// [HW] Axiom (well known): For OS devices' hardcoded TDs, they must be unchanged. (So they map to the same TD_Val across 
// state transitions)
// [NOTE] For hardcoded TDs of OS devices, WSM_MapOSTDVal_ToTDVal only needs to look at their values to output the 
// correct TD_Val. This makes sense because hardcoded TDs have already defined all possible transfers to the devices' objects
lemma {:axiom} Lemma_OSDevs_HCodedTDsMapToUnchangedVals(s1:state, s2:state)
    requires WK_ValidSubjs(s1.subjects, s1.id_mappings)
    requires WK_ValidObjs(s1.subjects, s1.objects)

    requires WK_ValidSubjs_SubjIDs(s2.subjects)
    requires WK_ValidObjs_ObjIDs(s2.objects)
    requires WK_ValidObjs_ObjInSubjsMustBeInState(s2.subjects, s2.objects)
        // Requirement: Unique subject ID, object ID, etc.

    requires MapGetKeys(s1.subjects.os_devs) == MapGetKeys(s2.subjects.os_devs)
    requires forall id :: id in s1.subjects.os_devs
                ==> (s1.subjects.os_devs[id].hcoded_td_id == s2.subjects.os_devs[id].hcoded_td_id &&
                     s1.subjects.os_devs[id].td_ids == s2.subjects.os_devs[id].td_ids &&
                     s1.subjects.os_devs[id].fd_ids == s2.subjects.os_devs[id].fd_ids &&
                     s1.subjects.os_devs[id].do_ids == s2.subjects.os_devs[id].do_ids)
        // Requirement: Same object ownership and hardcoded TDs of OS devices
    requires MapGetKeys(s1.objects.os_tds) == MapGetKeys(s2.objects.os_tds)
        // Requirement: Unchanged set of OS TDs
    requires forall id :: id in s1.subjects.os_devs
                ==> s1.subjects.os_devs[id].hcoded_td_id in s1.objects.os_tds
        // Requirement: OS devices' hardcoded TDs are in <os_tds>
    requires forall id :: id in s1.subjects.os_devs
                ==> s1.objects.os_tds[s1.subjects.os_devs[id].hcoded_td_id].val == s2.objects.os_tds[s2.subjects.os_devs[id].hcoded_td_id].val
        // Requirement: OS devices' hardcoded TDs have unchanged values

    ensures forall dev_id :: dev_id in s1.subjects.os_devs
                ==> WSM_MapOSTDVal_ToTDVal(s1.objects, s1.objects.os_tds[s1.subjects.os_devs[dev_id].hcoded_td_id].val) ==
                    WSM_MapOSTDVal_ToTDVal(s2.objects, s2.objects.os_tds[s2.subjects.os_devs[dev_id].hcoded_td_id].val)




/*********************** Utility Functions - General Objects ********************/
// Function: Return the PID of the given object
function WSM_ObjPID(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, id:Object_ID) : WS_PartitionID
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)

    requires WSM_IsObjID(objs, id)
{
    if(WSM_IsOSObj(objs, id)) then
        ObjPID_OSObj(objs, id)
    else if (WSM_IsEEHCIObj(objs, id)) then
        ObjPID_EEHCIObj(subjs, objs, id_mappings, globals, id)
    else if (WSM_IsUSBPDevObj(objs, id)) then
        ObjPID_USBPDevObj(subjs, objs, id_mappings, globals, id)
    else if (WSM_IsWimpDrvDO(objs, id)) then
        ObjPID_WimpDrvObj(subjs, objs, id_mappings, globals, id)
    else
        assert WSM_IsUSBTDMappedObj(objs, id);
        ObjPID_USBTDMappedObjs(subjs, objs, id_mappings, globals, id)
}

predicate WSM_IsActiveObj(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, id:Object_ID)
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)

    requires WSM_IsObjID(objs, id)
{
    WSM_ObjPID(subjs, objs, id_mappings, globals, id) != WS_PartitionID(PID_INVALID)
}





/*********************** Utility Functions - WimpDrvs' Objects ********************/
// Function: Return the ID of the wimp driver owning the given DO
function WimpDrvDO_FindOwner(subjs:WSM_Subjects, objs:WSM_Objects, id:Object_ID) : (result:Drv_ID)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs(subjs, objs)
    requires WSM_IsWimpDrvDO(objs, id)

    ensures WSM_IsWimpDrvID(subjs, result)
    ensures WSM_DoOwnObj(subjs, result.sid, id)
    ensures subjs.wimp_drvs[result].do_id == DO_ID(id)
{
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_InternalObjsOf_WimpSubjects();

    var drv_id :| drv_id in subjs.wimp_drvs &&
                  WSM_DoOwnObj(subjs, drv_id.sid, id);

    drv_id
}

// Function: return the PID of the given wimp drivers' object
function ObjPID_WimpDrvObj(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, id:Object_ID) : WS_PartitionID
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WSM_IsWimpDrvDO(objs, id)
{
    var drv_id := WimpDrvDO_FindOwner(subjs, objs, id);

    SubjPID_WimpDrv_ByDrvID(subjs, objs, id_mappings, globals, drv_id)
}




/*********************** Utility Functions - USB TDs ********************/
// Predicate: In <g_usbtd_map_mem>, exists a slot containing the given <id_word> 
predicate usbtd_idword_in_record(globals:globalsmap, id_word:word)
    requires WK_ValidGlobalVars_Decls(globals)
{
    exists slot :: usbtd_map_valid_slot_id(slot) &&
                    usbtd_map_get_idword(globals, slot) == id_word
}

// Function: Given a USB TD's ID, get the corrsponding usbtd_idword 
function USBTD_ID_ToIDWord(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, usbtd_id:TD_ID) : (result:word)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires usbtd_id in objs.usbtd_tds

    ensures result != USBTD_ID_INVALID
{
    reveal WK_ValidSubjs();
    reveal WK_ValidIDMappings_AdditonalPredicatesOfUSBTDObjs();
    reveal WK_ValidIDMappings();

    var id_word :| id_word in id_mappings.usbtd_to_td &&
                        id_mappings.usbtd_to_td[id_word] == usbtd_id;

    id_word
}

// Return the unique slot that contains the <id_word> in <g_usbtd_map_mem>
function usbtd_get_slot_by_idword(globals:globalsmap, id_word:word) : (slot:word)
    requires WK_ValidGlobalState(globals)
    requires usbtd_idword_in_record(globals, id_word)
    requires id_word != USBTD_ID_INVALID

    ensures usbtd_map_valid_slot_id(slot)
    ensures p_usbtd_slot_idword_unique(globals, slot, id_word)
{
    var v :| usbtd_map_valid_slot_id(v) &&
            usbtd_map_get_idword(globals, v) == id_word;

    v
}

// Return the PID of a USB TD. 
// If the USB TD has a record in <g_usbtd_map_mem>, return the PID in the record. Otherwise, the driver must be
// inactive, and hence return WS_PartitionID(PID_INVALID) 
function ObjPID_USBTD_ByIDWord(globals:globalsmap, id_word:word) : WS_PartitionID
    requires WK_ValidGlobalState(globals)
    requires id_word != USBTD_ID_INVALID
{
    if(usbtd_idword_in_record(globals, id_word)) then
        var usbtd_slot := usbtd_get_slot_by_idword(globals, id_word);
        usbtd_map_get_pid(globals, usbtd_slot)
    else
       WS_PartitionID(PID_INVALID) 
}

// Function: Return the ID word of the USB TD mapping to the given object
function USBTDMappedObj_IDToUSBTDIDWord(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, id:Object_ID) : (result:word)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs(subjs, objs)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WSM_IsUSBTDMappedObj(objs, id)

    ensures (result in id_mappings.usbtd_to_td &&
             id_mappings.usbtd_to_td[result] == TD_ID(id)) ||
            (result in id_mappings.usbtd_to_fd &&
             id_mappings.usbtd_to_fd[result] == FD_ID(id)) ||
            (result in id_mappings.usbtd_to_do &&
             id_mappings.usbtd_to_do[result] == DO_ID(id))
{
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_InternalObjsOf_WimpSubjects();

    reveal WK_ValidIDMappings();
    reveal WK_ValidIDMappings_AdditonalPredicatesOfUSBTDObjs();

    assert MapGetKeys(id_mappings.usbtd_to_td) == MapGetKeys(id_mappings.usbtd_to_fd) == MapGetKeys(id_mappings.usbtd_to_do);

    var idword :| idword != USBTD_ID_INVALID &&
                  (id_mappings.usbtd_to_td[idword] == TD_ID(id) || id_mappings.usbtd_to_fd[idword] == FD_ID(id) || id_mappings.usbtd_to_do[idword] == DO_ID(id));

    idword
}

// Function: return the PID of the given object that map to a USBTD
function ObjPID_USBTDMappedObjs(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, id:Object_ID) : WS_PartitionID
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WSM_IsUSBTDMappedObj(objs, id)
{
    var idword := USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, id);

    ObjPID_USBTD_ByIDWord(globals, idword)
}




/*********************** Utility Functions - USBPDevs' Objects ********************/
// Function: Return the ID of the USBPDev owning the given object
function USBPDevObj_FindOwner(subjs:WSM_Subjects, objs:WSM_Objects, id:Object_ID) : (result:Dev_ID)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidObjs(subjs, objs)
    requires WSM_IsUSBPDevObj(objs, id)

    ensures WSM_IsUSBPDevID(subjs, result)
    ensures WSM_DoOwnObj(subjs, result.sid, id)
{
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_InternalObjsOf_WimpSubjects();

    var dev_id :| dev_id in subjs.usbpdevs &&
            WSM_DoOwnObj(subjs, dev_id.sid, id);

    dev_id
}

// Function: return the PID of the given USBPDev's object
function ObjPID_USBPDevObj(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, id:Object_ID) : WS_PartitionID
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WSM_IsUSBPDevObj(objs, id)
{
    var dev_id := USBPDevObj_FindOwner(subjs, objs, id);

    SubjPID_USBPDev_ByDevID(subjs, objs, id_mappings, globals, dev_id)
}




/*********************** Utility Functions - eEHCIs' Objects ********************/
function method EEHCI_GetHCodedTDVal(subjs:WSM_Subjects, objs:WSM_Objects, eehci_id:Dev_ID) : TD_Val
    requires WK_ValidObjs_ObjInSubjsMustBeInState(subjs, objs)
    requires WSM_IsEEHCIDevID(subjs, eehci_id)
{
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();
    
    var hcoded_td_id := subjs.eehcis[eehci_id].hcoded_td_id;
    assert hcoded_td_id in objs.eehci_hcoded_tds;
    var hcoded_td_val := objs.eehci_hcoded_tds[hcoded_td_id];

    hcoded_td_val
}

// Function: Return the ID of the eEHCI owning the given object
function EEHCIObj_FindOwner(subjs:WSM_Subjects, objs:WSM_Objects, id:Object_ID) : (result:Dev_ID)
    requires WK_ValidSubjs_SubjIDs(subjs)
    requires WK_ValidSubjs_eEHCIs(subjs)
    requires WK_ValidObjs(subjs, objs)
    requires WSM_IsEEHCIObj(objs, id)

    ensures WSM_IsEEHCIDevID(subjs, result)
    ensures WSM_DoOwnObj(subjs, result.sid, id)
{
    reveal WK_ValidSubjs_SubjIDs();
    reveal WK_ValidSubjs_eEHCIs();
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_InternalObjsOf_WimpSubjects();

    var dev_id :| dev_id in subjs.eehcis &&
            (TD_ID(id) == subjs.eehcis[dev_id].hcoded_td_id || TD_ID(id) in OwnedTDs_eEHCI_ExcludeHCodedTD(subjs, dev_id) ||
             FD_ID(id) in subjs.eehcis[dev_id].fd_ids || DO_ID(id) in subjs.eehcis[dev_id].do_ids);

    assert WSM_DoOwnObj(subjs, dev_id.sid, id);

    dev_id
}

// Function: return the PID of the given eEHCI's object
function ObjPID_EEHCIObj(subjs:WSM_Subjects, objs:WSM_Objects, id_mappings:WSM_ID_Mappings, globals:globalsmap, id:Object_ID) : WS_PartitionID
    requires WK_ValidGlobalState(globals)
    requires WK_ValidSubjs(subjs, id_mappings)
    requires WK_ValidIDMappings(subjs, objs, id_mappings)
    requires WK_ValidObjs(subjs, objs)
    requires WSM_IsEEHCIObj(objs, id)
{
    var dev_id := EEHCIObj_FindOwner(subjs, objs, id);

    SubjPID_EEHCI_ByDevID(subjs, objs, id_mappings, globals, dev_id)
}




/*********************** Utility Lemmas ********************/
lemma Lemma_WSM_AllHCodedTDIDs_Properties(s:state)
    requires WK_ValidSubjs_SubjIDs(s.subjects)
    requires WK_ValidObjs(s.subjects, s.objects)

    ensures WSM_AllHCodedTDIDs(s.subjects) <= WSM_AllTDIDs(s.objects)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    forall id | id in WSM_AllHCodedTDIDs(s.subjects)
        ensures id in WSM_AllTDIDs(s.objects)
    {
        if(id in WSM_AllHCodedTDIDs_OSDevs(s.subjects))
        {
            var dev_id :| dev_id in s.subjects.os_devs && s.subjects.os_devs[dev_id].hcoded_td_id == id;
            assert id in s.objects.os_tds;
            assert id in WSM_AllTDIDs(s.objects);
        }
        else if(id in WSM_AllHCodedTDIDs_USBPDevs(s.subjects))
        {
            assert id in WSM_AllTDIDs(s.objects);
        }
        else
        {
            assert id in WSM_AllHCodedTDIDs_EEHCIs(s.subjects);
            assert id in WSM_AllTDIDs(s.objects);
        }
    }
}

lemma Lemma_WSM_AllHCodedTDIDs_NotInEEHCIOtherTDs(s:state)
    requires WK_ValidSubjs_SubjIDs(s.subjects)
    requires WK_ValidObjs(s.subjects, s.objects)

    ensures forall id :: id in WSM_AllHCodedTDIDs(s.subjects)
                ==> id !in s.objects.eehci_other_tds
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    forall id | id in WSM_AllHCodedTDIDs(s.subjects)
        ensures id !in s.objects.eehci_other_tds
    {
        if(id in WSM_AllHCodedTDIDs_OSDevs(s.subjects))
        {
            var dev_id :| dev_id in s.subjects.os_devs && s.subjects.os_devs[dev_id].hcoded_td_id == id;
            assert id in s.objects.os_tds;
            assert id !in s.objects.eehci_other_tds;
        }
        else if(id in WSM_AllHCodedTDIDs_USBPDevs(s.subjects))
        {
            assert id !in s.objects.eehci_other_tds;
        }
        else
        {
            assert id in WSM_AllHCodedTDIDs_EEHCIs(s.subjects);
            assert id !in s.objects.eehci_other_tds;
        }
    }
}