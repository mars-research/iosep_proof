include "Syntax.dfy"
include "./utils/Collections.dfy"
include "Utils_SlimState.dfy"

//******** Subjects/Objects ID  ********//
// Convert the set of Drv_ID to Subject_ID
function method DrvIDsToSubjIDs(drv_ids:set<Drv_ID>) : set<Subject_ID>
    ensures forall subj_id :: Drv_ID(subj_id) in drv_ids
                <==> subj_id in DrvIDsToSubjIDs(drv_ids)
{
    Lemma_SameIDsIffSameInternalIDs();
    set drv_id, id | drv_id in drv_ids && drv_id.sid == id :: id
}

// Convert the set of Dev_ID to Subject_ID
function method DevIDsToSubjIDs(dev_ids:set<Dev_ID>) : set<Subject_ID>
    ensures forall subj_id :: Dev_ID(subj_id) in dev_ids
                <==> subj_id in DevIDsToSubjIDs(dev_ids)
{
    Lemma_SameIDsIffSameInternalIDs();
    set dev_id, id | dev_id in dev_ids && dev_id.sid == id :: id
}

// Convert the set of TD_ID to Object_ID
function method TDIDsToObjIDs(td_ids:set<TD_ID>) : set<Object_ID>
    ensures forall id :: TD_ID(id) in td_ids
                <==> id in TDIDsToObjIDs(td_ids)
{
    Lemma_SameIDsIffSameInternalIDs();
    set td_id, id | td_id in td_ids && td_id.oid == id :: id
}

// Convert the set of FD_ID to Object_ID
function method FDIDsToObjIDs(fd_ids:set<FD_ID>) : set<Object_ID>
    ensures forall id :: FD_ID(id) in fd_ids
                <==> id in FDIDsToObjIDs(fd_ids)
{
    Lemma_SameIDsIffSameInternalIDs();
    set fd_id, id | fd_id in fd_ids && fd_id.oid == id :: id
}

// Convert the set of DO_ID to Object_ID
function method DOIDsToObjIDs(do_ids:set<DO_ID>) : set<Object_ID>
    ensures forall id :: DO_ID(id) in do_ids
                <==> id in DOIDsToObjIDs(do_ids)
{
    Lemma_SameIDsIffSameInternalIDs();
    set do_id, id | do_id in do_ids && do_id.oid == id :: id
}

function method IsDevID(k:State, dev_id:Dev_ID) : bool
    ensures IsDevID(k, dev_id) == IsDevID_SlimState(k.subjects, dev_id)
{
    IsDevID_SlimState(k.subjects, dev_id)
}

function method IsDrvID(k:State, drv_id:Drv_ID) : bool
{
    drv_id in k.subjects.drvs
}

// Is the object (id == <o_id>) is a TD?
function method IsTD(k:State, o_id:Object_ID) : bool
{
    TD_ID(o_id) in AllTDIDs(k.objects)
}

// Get the TD state mapped to the <td_id>
function method IDToTD(tds:map<TD_ID, TD_State>, td_id:TD_ID) : TD_State
    requires td_id in tds
{
    tds[td_id]
}

// Is the object (id == <o_id>) is a FD?
function method IsFD(k:State, o_id:Object_ID) : bool
{
    FD_ID(o_id) in AllFDIDs(k.objects)
}

// Is the object (id == <o_id>) is a DO?
function method IsDO(k:State, o_id:Object_ID) : bool
{
    DO_ID(o_id) in AllDOIDs(k.objects)
}

// Get the driver state mapped to the <drv_id>
function method IDToDrv(k:State, drv_id:Drv_ID) : Drv_State
    requires drv_id in k.subjects.drvs
{
    k.subjects.drvs[drv_id]
}

// Get the device state mapped to the <dev_id>
function method IDToDev(k:State, dev_id:Dev_ID) : Dev_State
    requires dev_id in k.subjects.devs
    ensures IDToDev(k, dev_id) == IDToDev_SlimState(k.subjects, dev_id)
{
    IDToDev_SlimState(k.subjects, dev_id)
}

// Return if the TD (<td_id>) is referenced in the <td_state>
function method DoRefTD(td_state:TD_Val, td_id:TD_ID) : bool
    ensures DoRefTD(td_state, td_id) == true
                <==> td_id in td_state.trans_params_tds
{
    td_id in td_state.trans_params_tds
}




//******** Objects Ownership ********//
// Does the subject (id == <s_id> own the object (id == <o_id>)
function method DoOwnObj(k:State, s_id:Subject_ID, o_id:Object_ID) : bool
    requires IsSubjID(k.subjects, s_id)
    ensures DoOwnObj(k, s_id, o_id) == DoOwnObj_SlimState(k.subjects, s_id, o_id)
{
    DoOwnObj_SlimState(k.subjects, s_id, o_id)
}

predicate P_ObjsInSubjsAreAlsoInState(k:State)
{
    (forall drv_id :: drv_id in k.subjects.drvs
                ==> (forall td_id :: td_id in k.subjects.drvs[drv_id].td_ids
                        ==> td_id.oid in AllObjsIDs(k.objects)) &&
                    (forall fd_id :: fd_id in k.subjects.drvs[drv_id].fd_ids
                        ==> fd_id.oid in AllObjsIDs(k.objects)) &&
                    (forall do_id :: do_id in k.subjects.drvs[drv_id].do_ids
                        ==> do_id.oid in AllObjsIDs(k.objects))) &&
    (forall dev_id :: dev_id in k.subjects.devs
                ==> (forall td_id :: td_id in k.subjects.devs[dev_id].td_ids
                        ==> td_id.oid in AllObjsIDs(k.objects)) &&
                    (forall fd_id :: fd_id in k.subjects.devs[dev_id].fd_ids
                        ==> fd_id.oid in AllObjsIDs(k.objects)) &&
                    (forall do_id :: do_id in k.subjects.devs[dev_id].do_ids
                        ==> do_id.oid in AllObjsIDs(k.objects))) &&

    (true)
}

// Return the IDs of all objects owned by the subject (id == <s_id>)
function method OwnObjIDs(k:State, s_id:Subject_ID) : set<Object_ID>
    requires P_ObjsInSubjsAreAlsoInState(k)
    requires IsSubjID(k.subjects, s_id) 
    ensures OwnObjIDs(k, s_id) <= AllObjsIDs(k.objects)
{
    if(Drv_ID(s_id) in k.subjects.drvs) then
        TDIDsToObjIDs(k.subjects.drvs[Drv_ID(s_id)].td_ids) +
        FDIDsToObjIDs(k.subjects.drvs[Drv_ID(s_id)].fd_ids) +
        DOIDsToObjIDs(k.subjects.drvs[Drv_ID(s_id)].do_ids)
    else
        TDIDsToObjIDs(k.subjects.devs[Dev_ID(s_id)].td_ids) +
        FDIDsToObjIDs(k.subjects.devs[Dev_ID(s_id)].fd_ids) +
        DOIDsToObjIDs(k.subjects.devs[Dev_ID(s_id)].do_ids)
}

function method OwnedTDs(k:State, s_id:Subject_ID) : set<TD_ID>
    requires IsSubjID(k.subjects, s_id)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)

    ensures OwnedTDs(k, s_id) == OwnedTDs_SlimState(k.subjects, s_id)
{
    OwnedTDs_SlimState(k.subjects, s_id)
}

function method OwnedFDs(k:State, s_id:Subject_ID) : set<FD_ID>
    requires IsSubjID(k.subjects, s_id)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)
    ensures OwnedFDs(k, s_id) == OwnedFDs_SlimState(k.subjects, s_id)
{
    OwnedFDs_SlimState(k.subjects, s_id)
}

function method OwnedDOs(k:State, s_id:Subject_ID) : set<DO_ID>
    requires IsSubjID(k.subjects, s_id)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)
    ensures OwnedDOs(k, s_id) == OwnedDOs_SlimState(k.subjects, s_id)
{
    OwnedDOs_SlimState(k.subjects, s_id)
}




//******** Partition ID  ********//
// Return the ID of the partition that the subject (id == <s_id>)
// belongs to.
// Return NULL if the subject does not belong to any partition 
function method SubjPID(k:State, s_id:Subject_ID): Partition_ID
    requires IsSubjID(k.subjects, s_id)
    ensures SubjPID(k, s_id) == SubjPID_SlimState(k.subjects, s_id)
{
    SubjPID_SlimState(k.subjects, s_id)
}

// Return the ID of the partition that the object (id == <o_id>) 
// belongs to. 
// Return NULL if the object does not belong to any partition 
function method ObjPID(k:State, o_id:Object_ID) : Partition_ID
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs
    requires o_id in AllObjsIDs(k.objects)

    ensures (TD_ID(o_id) in k.objects.active_non_hcoded_tds ==> BuildMap_ObjIDsToPIDs(k.objects)[o_id] == k.objects.active_non_hcoded_tds[TD_ID(o_id)].pid) &&
            (FD_ID(o_id) in k.objects.active_fds ==> BuildMap_ObjIDsToPIDs(k.objects)[o_id] == k.objects.active_fds[FD_ID(o_id)].pid) &&
            (DO_ID(o_id) in k.objects.active_dos ==> BuildMap_ObjIDsToPIDs(k.objects)[o_id] == k.objects.active_dos[DO_ID(o_id)].pid) &&
            (TD_ID(o_id) in k.objects.inactive_non_hcoded_tds ==> BuildMap_ObjIDsToPIDs(k.objects)[o_id] == NULL) &&
            (FD_ID(o_id) in k.objects.inactive_fds ==> BuildMap_ObjIDsToPIDs(k.objects)[o_id] == NULL) &&
            (DO_ID(o_id) in k.objects.inactive_dos ==> BuildMap_ObjIDsToPIDs(k.objects)[o_id] == NULL) &&
            (TD_ID(o_id) in k.objects.hcoded_tds ==> BuildMap_ObjIDsToPIDs(k.objects)[o_id] == k.objects.hcoded_tds[TD_ID(o_id)].pid)

    ensures ObjPID_KObjects(k.objects, o_id) == ObjPID(k, o_id)
{
    ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k.objects), o_id)
}

function method ObjPID_KObjects(k_objects:Objects, o_id:Object_ID) : Partition_ID
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
        // Requirement: Objects have different internal IDs
    requires o_id in AllObjsIDs(k_objects)

    ensures (TD_ID(o_id) in k_objects.active_non_hcoded_tds ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == k_objects.active_non_hcoded_tds[TD_ID(o_id)].pid) &&
                    (FD_ID(o_id) in k_objects.active_fds ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == k_objects.active_fds[FD_ID(o_id)].pid) &&
                    (DO_ID(o_id) in k_objects.active_dos ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == k_objects.active_dos[DO_ID(o_id)].pid) &&
                    (TD_ID(o_id) in k_objects.inactive_non_hcoded_tds ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == NULL) &&
                    (FD_ID(o_id) in k_objects.inactive_fds ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == NULL) &&
                    (DO_ID(o_id) in k_objects.inactive_dos ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == NULL) &&
                    (TD_ID(o_id) in k_objects.hcoded_tds ==> BuildMap_ObjIDsToPIDs(k_objects)[o_id] == k_objects.hcoded_tds[TD_ID(o_id)].pid)
{
    ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id)
}

// Return the ID of the partition that the device (id == <dev_id>)
// belongs to.
// Return NULL if the device does not belong to any partition 
function method SubjPID_DevID(k:State, dev_id:Dev_ID): Partition_ID
    requires IsDevID(k, dev_id)
    ensures SubjPID_DevID(k, dev_id) == SubjPID_DevID_SlimState(k.subjects, dev_id)
{
    SubjPID_DevID_SlimState(k.subjects, dev_id)
}




//******** Active/Inactive Subjects/Objects  ********//
// Return all active subjects in the current state <k>
function method AllActiveSubjs(k:State) : set<Subject_ID>
    ensures AllActiveSubjs(k) == AllActiveSubjs_SlimState(k.subjects)
{
    AllActiveSubjs_SlimState(k.subjects)
}

// Return all active objects in the current state <k>
function method AllActiveObjs(k:State) : set<Object_ID>
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs

    ensures AllActiveObjs(k) == AllActiveObjs_SlimState(k.objects)
{
    AllActiveObjs_SlimState(k.objects)
}

function method AllActiveTDs(k:State) : set<TD_ID>
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    ensures AllActiveTDs(k) == AllActiveTDs_SlimState(k.objects)
{
    AllActiveTDs_SlimState(k.objects)
}

function method AllActiveFDs(k:State) : set<FD_ID>
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    ensures AllActiveFDs(k) == AllActiveFDs_SlimState(k.objects)
{
    AllActiveFDs_SlimState(k.objects)
}

function method AllActiveDOs(k:State) : set<DO_ID>
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    ensures AllActiveDOs(k) == AllActiveDOs_SlimState(k.objects)
{
    AllActiveDOs_SlimState(k.objects)
}

function method TDsToTDsVals(tds:map<TD_ID, TD_State>) : map<TD_ID, TD_Val>
    ensures MapGetKeys(TDsToTDsVals(tds)) == MapGetKeys(tds)
{
    map td_id | td_id in tds
              :: tds[td_id].val
}

// Get the current state of active TDs of <k>
function method ActiveTDsState(k:State) : map<TD_ID, TD_Val>
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    ensures MapGetKeys(ActiveTDsState(k)) == AllActiveTDs(k)
    ensures ActiveTDsState(k) == ActiveTDsState_SlimState(k.objects)
{
    ActiveTDsState_SlimState(k.objects)
}

// Return all active devices in the current state <k>
function method AllActiveDrvs(k:State) : set<Drv_ID>
    ensures AllActiveDrvs(k) == AllActiveDrvs_SlimState(k.subjects)
{
    AllActiveDrvs_SlimState(k.subjects)
}

// Return all active devices in the current state <k>
function method AllActiveDevs(k:State) : set<Dev_ID>
    ensures AllActiveDevs(k) == AllActiveDevs_SlimState(k.subjects)
{
    AllActiveDevs_SlimState(k.subjects)
}

// Return all active subjects in the partition (id == <pid>)
function method ActiveSubjsInPartition(k:State, pid:Partition_ID) : set<Subject_ID>
    requires pid != NULL

    ensures ActiveSubjsInPartition(k, pid) <= AllActiveSubjs(k)
{
    set s_id | s_id in AllSubjsIDs(k.subjects) && SubjPID(k, s_id) == pid :: s_id 
}

// Return all active objects in the partition (id == <pid>)
function method ActiveObjsInPartition(k:State, pid:Partition_ID) : set<Object_ID>
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs

    requires pid != NULL

    ensures ActiveObjsInPartition(k, pid) <= AllActiveObjs(k)
{
    set o_id |  o_id in AllObjsIDs(k.objects) && 
                ObjPID(k, o_id) == pid
             :: o_id
}

// Return all active devices in the partition (id == <pid>)
function method ActiveDevsInPartition(
    k_subjects:Subjects, pid:Partition_ID
) : set<Dev_ID>
    requires pid != NULL

    ensures ActiveDevsInPartition(k_subjects, pid) <= AllActiveDevs_SlimState(k_subjects)
{
    set dev_id | dev_id in k_subjects.devs && SubjPID_SlimState(k_subjects, dev_id.sid) == pid :: dev_id 
}




//******** TDs/FDs/DOs  ********//
function method TDRefedObjs(td:TD_Val) : set<Object_ID>
{
    TDIDsToObjIDs(MapGetKeys(td.trans_params_tds)) + 
    FDIDsToObjIDs(MapGetKeys(td.trans_params_fds)) +
    DOIDsToObjIDs(MapGetKeys(td.trans_params_dos))
}

function method IsTDClearVal(tds:map<TD_ID, TD_State>, td_id:TD_ID) : bool
    requires td_id in tds
{
    tds[td_id].val == TD_Val(map[], map[], map[])
}

function method IsFDClearVal(fds:map<FD_ID, FD_State>, fd_id:FD_ID) : bool
    requires fd_id in fds
{
    fds[fd_id].val == FD_Val("")
}

function method IsDOClearVal(dos:map<DO_ID, DO_State>, do_id:DO_ID) : bool
    requires do_id in dos
{
    dos[do_id].val == DO_Val("")
}

function method WriteActiveNonHCodedTDsVals(
    k_objects:Objects, td_id_val_map:map<TD_ID, TD_Val>
) : (result:Objects)
    requires forall td_id:: td_id in td_id_val_map ==> td_id in k_objects.active_non_hcoded_tds

    ensures k_objects.active_fds == result.active_fds &&
            k_objects.active_dos == result.active_dos &&
            k_objects.inactive_non_hcoded_tds == result.inactive_non_hcoded_tds &&
            k_objects.inactive_fds == result.inactive_fds &&
            k_objects.inactive_dos == result.inactive_dos &&
            k_objects.hcoded_tds == result.hcoded_tds
    ensures MapGetKeys(k_objects.active_non_hcoded_tds) == MapGetKeys(result.active_non_hcoded_tds)
        // Property: Other fields in <k_objects> must be unchanged
    ensures forall td_id :: td_id in k_objects.active_non_hcoded_tds
                ==> (td_id in td_id_val_map ==> result.active_non_hcoded_tds[td_id].val == td_id_val_map[td_id]) &&
                    (td_id !in td_id_val_map ==> result.active_non_hcoded_tds[td_id] == k_objects.active_non_hcoded_tds[td_id])
        // Property: The values in <td_id_val_map> is written into result
    ensures forall td_id :: td_id in k_objects.active_non_hcoded_tds
                ==> k_objects.active_non_hcoded_tds[td_id].pid == result.active_non_hcoded_tds[td_id].pid
        // Property: WriteTD does not change the pids of any TDs
{
    var new_active_non_hcoded_tds := map td_id | td_id in k_objects.active_non_hcoded_tds 
                                            :: if td_id !in td_id_val_map then 
                                                    k_objects.active_non_hcoded_tds[td_id] 
                                            else 
                                                    TD_State(k_objects.active_non_hcoded_tds[td_id].pid, td_id_val_map[td_id]);

    k_objects.(active_non_hcoded_tds := new_active_non_hcoded_tds)
}

function method WriteActiveFDsVals(
    k_objects:Objects, fd_id_val_map:map<FD_ID, FD_Val>
) : (result:Objects)
    requires forall fd_id:: fd_id in fd_id_val_map ==> fd_id in k_objects.active_fds

    ensures k_objects.active_non_hcoded_tds == result.active_non_hcoded_tds &&
            k_objects.active_dos == result.active_dos &&
            k_objects.inactive_non_hcoded_tds == result.inactive_non_hcoded_tds &&
            k_objects.inactive_fds == result.inactive_fds &&
            k_objects.inactive_dos == result.inactive_dos &&
            k_objects.hcoded_tds == result.hcoded_tds
    ensures MapGetKeys(k_objects.active_fds) == MapGetKeys(result.active_fds)
        // Property: Other fields in <k_objects> must be unchanged
    ensures forall fd_id :: fd_id in k_objects.active_fds
                ==> (fd_id in fd_id_val_map ==> result.active_fds[fd_id].val == fd_id_val_map[fd_id]) &&
                    (fd_id !in fd_id_val_map ==> result.active_fds[fd_id] == k_objects.active_fds[fd_id])
        // Property: The values in <fd_id_val_map> is written into result
    ensures forall fd_id :: fd_id in k_objects.active_fds
                ==> k_objects.active_fds[fd_id].pid == result.active_fds[fd_id].pid
        // Property: WriteFD does not change the pids of any FDs
{
    var new_active_fds := map fd_id | fd_id in k_objects.active_fds 
                                            :: if fd_id !in fd_id_val_map then 
                                                    k_objects.active_fds[fd_id] 
                                            else 
                                                    FD_State(k_objects.active_fds[fd_id].pid, fd_id_val_map[fd_id]);

    k_objects.(active_fds := new_active_fds)
}

function method WriteActiveDOsVals(
    k_objects:Objects, do_id_val_map:map<DO_ID, DO_Val>
) : (result:Objects)
    requires forall do_id:: do_id in do_id_val_map ==> do_id in k_objects.active_dos

    ensures k_objects.active_non_hcoded_tds == result.active_non_hcoded_tds &&
            k_objects.active_fds == result.active_fds &&
            k_objects.inactive_non_hcoded_tds == result.inactive_non_hcoded_tds &&
            k_objects.inactive_fds == result.inactive_fds &&
            k_objects.inactive_dos == result.inactive_dos &&
            k_objects.hcoded_tds == result.hcoded_tds
    ensures MapGetKeys(k_objects.active_dos) == MapGetKeys(result.active_dos)
        // Property: Other fields in <k_objects> must be unchanged
    ensures forall do_id :: do_id in k_objects.active_dos
                ==> (do_id in do_id_val_map ==> result.active_dos[do_id].val == do_id_val_map[do_id]) &&
                    (do_id !in do_id_val_map ==> result.active_dos[do_id] == k_objects.active_dos[do_id])
        // Property: The values in <do_id_val_map> is written into result
    ensures forall do_id :: do_id in k_objects.active_dos
                ==> k_objects.active_dos[do_id].pid == result.active_dos[do_id].pid
        // Property: WriteDO does not change the pids of any DOs
{
    var new_active_dos := map do_id | do_id in k_objects.active_dos 
                                            :: if do_id !in do_id_val_map then 
                                                    k_objects.active_dos[do_id] 
                                            else 
                                                    DO_State(k_objects.active_dos[do_id].pid, do_id_val_map[do_id]);

    k_objects.(active_dos := new_active_dos)
}

function method ClearActiveNonHCodedTDs(
    k_objects:Objects, clear_tds:set<TD_ID>
) : (result:Objects)
    requires forall td_id:: td_id in clear_tds ==> td_id in k_objects.active_non_hcoded_tds

    ensures k_objects.active_fds == result.active_fds &&
            k_objects.active_dos == result.active_dos &&
            k_objects.inactive_non_hcoded_tds == result.inactive_non_hcoded_tds &&
            k_objects.inactive_fds == result.inactive_fds &&
            k_objects.inactive_dos == result.inactive_dos &&
            k_objects.hcoded_tds == result.hcoded_tds
    ensures MapGetKeys(k_objects.active_non_hcoded_tds) == MapGetKeys(result.active_non_hcoded_tds)
        // Property: Other fields in <k_objects> must be unchanged
    ensures forall td_id :: td_id in k_objects.active_non_hcoded_tds
                ==> (td_id in clear_tds ==> result.active_non_hcoded_tds[td_id].val == TD_Val(map[], map[], map[])) &&
                    (td_id !in clear_tds ==> result.active_non_hcoded_tds[td_id] == k_objects.active_non_hcoded_tds[td_id])
        // Property: In the result, the values of TDs to be cleared are empty
    ensures forall td_id :: td_id in k_objects.active_non_hcoded_tds
                ==> k_objects.active_non_hcoded_tds[td_id].pid == result.active_non_hcoded_tds[td_id].pid
        // Property: WriteTD does not change the pids of any TDs
{
    var new_active_non_hcoded_tds := map td_id | td_id in k_objects.active_non_hcoded_tds  
                                        :: if td_id !in clear_tds then 
                                                k_objects.active_non_hcoded_tds[td_id] 
                                           else 
                                                TD_State(k_objects.active_non_hcoded_tds [td_id].pid, TD_Val(map[], map[], map[]));
    k_objects.(active_non_hcoded_tds := new_active_non_hcoded_tds)
}

function method ClearActiveFDs(
    k_objects:Objects, clear_fds:set<FD_ID>
) : (result:Objects)
    requires forall fd_id:: fd_id in clear_fds ==> fd_id in k_objects.active_fds

    ensures k_objects.active_non_hcoded_tds == result.active_non_hcoded_tds &&
            k_objects.active_dos == result.active_dos &&
            k_objects.inactive_non_hcoded_tds == result.inactive_non_hcoded_tds &&
            k_objects.inactive_fds == result.inactive_fds &&
            k_objects.inactive_dos == result.inactive_dos &&
            k_objects.hcoded_tds == result.hcoded_tds
    ensures MapGetKeys(k_objects.active_fds) == MapGetKeys(result.active_fds)
        // Property: Other fields in <k_objects> must be unchanged
    ensures forall fd_id :: fd_id in k_objects.active_fds
                ==> (fd_id in clear_fds ==> result.active_fds[fd_id].val == FD_Val("")) &&
                    (fd_id !in clear_fds ==> result.active_fds[fd_id] == k_objects.active_fds[fd_id])
        // Property: In the result, the values of FDs to be cleared are empty
    ensures forall fd_id :: fd_id in k_objects.active_fds
                ==> k_objects.active_fds[fd_id].pid == result.active_fds[fd_id].pid
        // Property: WriteFD does not change the pids of any FDs
{
    var new_active_fds := map fd_id | fd_id in k_objects.active_fds  
                                        :: if fd_id !in clear_fds then 
                                                k_objects.active_fds[fd_id] 
                                           else 
                                                FD_State(k_objects.active_fds [fd_id].pid, FD_Val(""));
    k_objects.(active_fds := new_active_fds)
}

function method ClearActiveDOs(
    k_objects:Objects, clear_dos:set<DO_ID>
) : (result:Objects)
    requires forall do_id:: do_id in clear_dos ==> do_id in k_objects.active_dos

    ensures k_objects.active_non_hcoded_tds == result.active_non_hcoded_tds &&
            k_objects.active_fds == result.active_fds &&
            k_objects.inactive_non_hcoded_tds == result.inactive_non_hcoded_tds &&
            k_objects.inactive_fds == result.inactive_fds &&
            k_objects.inactive_dos == result.inactive_dos &&
            k_objects.hcoded_tds == result.hcoded_tds
    ensures MapGetKeys(k_objects.active_dos) == MapGetKeys(result.active_dos)
        // Property: Other fields in <k_objects> must be unchanged
    ensures forall do_id :: do_id in k_objects.active_dos
                ==> (do_id in clear_dos ==> result.active_dos[do_id].val == DO_Val("")) &&
                    (do_id !in clear_dos ==> result.active_dos[do_id] == k_objects.active_dos[do_id])
        // Property: In the result, the values of DOs to be cleared are empty
    ensures forall do_id :: do_id in k_objects.active_dos
                ==> k_objects.active_dos[do_id].pid == result.active_dos[do_id].pid
        // Property: WriteDO does not change the pids of any DOs
{
    var new_active_dos := map do_id | do_id in k_objects.active_dos  
                                        :: if do_id !in clear_dos then 
                                                k_objects.active_dos[do_id] 
                                           else 
                                                DO_State(k_objects.active_dos [do_id].pid, DO_Val(""));
    k_objects.(active_dos := new_active_dos)
}

function method SetPIDs_ActiveNonHCodedTDs_ToNULLPID(
    k_objects:Objects, tds_to_modify:set<TD_ID>
) : (result:Objects)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
    requires forall td_id:: td_id in tds_to_modify ==> td_id in k_objects.active_non_hcoded_tds

    ensures AllTDIDs(k_objects) == AllTDIDs(result)
    ensures AllFDIDs(k_objects) == AllFDIDs(result)
    ensures AllDOIDs(k_objects) == AllDOIDs(result)
    ensures AllObjsIDs(k_objects) == AllObjsIDs(result)

    ensures IsValidState_Objects_UniqueObjIDs(result)
        // Property: Object IDs are unchanged
    ensures forall td_id :: td_id in k_objects.inactive_non_hcoded_tds
                ==> td_id in result.inactive_non_hcoded_tds
    ensures forall td_id :: td_id in result.active_non_hcoded_tds
                ==> td_id in k_objects.active_non_hcoded_tds
        // Property: Inactive non-hcoded TDs become more, and active ones becomes less
    ensures forall td_id :: td_id in k_objects.active_non_hcoded_tds
                ==> (td_id in tds_to_modify ==> (td_id !in result.active_non_hcoded_tds && 
                                                 td_id in result.inactive_non_hcoded_tds)
                    ) &&
                    (td_id !in tds_to_modify ==> (td_id in result.active_non_hcoded_tds && 
                                                  result.active_non_hcoded_tds[td_id] == k_objects.active_non_hcoded_tds[td_id])
                    )
        // Property: Only the given active non-hcoded TDs <tds_to_modify> is put to the set 
        // <result.inactive_non_hcoded_tds>
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var new_active_non_hcoded_tds := MapRemoveKeys(k_objects.active_non_hcoded_tds, tds_to_modify);
    var new_inactive_non_hcoded_tds := SetConcat(k_objects.inactive_non_hcoded_tds, tds_to_modify);

    k_objects.(active_non_hcoded_tds := new_active_non_hcoded_tds, inactive_non_hcoded_tds := new_inactive_non_hcoded_tds)
}

function method SetPIDs_ActiveFDs_ToNULLPID(
    k_objects:Objects, fds_to_modify:set<FD_ID>
) : (result:Objects)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
    requires forall fd_id:: fd_id in fds_to_modify ==> fd_id in k_objects.active_fds

    ensures AllTDIDs(k_objects) == AllTDIDs(result)
    ensures AllFDIDs(k_objects) == AllFDIDs(result)
    ensures AllDOIDs(k_objects) == AllDOIDs(result)
    ensures AllObjsIDs(k_objects) == AllObjsIDs(result)

    ensures IsValidState_Objects_UniqueObjIDs(result)
        // Property: Object IDs are unchanged
    ensures forall fd_id :: fd_id in k_objects.inactive_fds
                ==> fd_id in result.inactive_fds
    ensures forall fd_id :: fd_id in result.active_fds
                ==> fd_id in k_objects.active_fds
        // Property: Inactive non-hcoded FDs become more, and active ones becomes less
    ensures forall fd_id :: fd_id in k_objects.active_fds
                ==> (fd_id in fds_to_modify ==> (fd_id !in result.active_fds && 
                                                 fd_id in result.inactive_fds)
                    ) &&
                    (fd_id !in fds_to_modify ==> (fd_id in result.active_fds && 
                                                  result.active_fds[fd_id] == k_objects.active_fds[fd_id])
                    )
        // Property: Only the given active FDs <fds_to_modify> is put to the set <result.inactive_fds>
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var new_active_fds := MapRemoveKeys(k_objects.active_fds, fds_to_modify);
    var new_inactive_fds := SetConcat(k_objects.inactive_fds, fds_to_modify);

    k_objects.(active_fds := new_active_fds, inactive_fds := new_inactive_fds)
}

function method SetPIDs_ActiveDOs_ToNULLPID(
    k_objects:Objects, dos_to_modify:set<DO_ID>
) : (result:Objects)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
    requires forall do_id:: do_id in dos_to_modify ==> do_id in k_objects.active_dos

    ensures AllTDIDs(k_objects) == AllTDIDs(result)
    ensures AllFDIDs(k_objects) == AllFDIDs(result)
    ensures AllDOIDs(k_objects) == AllDOIDs(result)
    ensures AllObjsIDs(k_objects) == AllObjsIDs(result)

    ensures IsValidState_Objects_UniqueObjIDs(result)
        // Property: Object IDs are unchanged
    ensures forall do_id :: do_id in k_objects.inactive_dos
                ==> do_id in result.inactive_dos
    ensures forall do_id :: do_id in result.active_dos
                ==> do_id in k_objects.active_dos
        // Property: Inactive non-hcoded DOs become more, and active ones becomes less
    ensures forall do_id :: do_id in k_objects.active_dos
                ==> (do_id in dos_to_modify ==> (do_id !in result.active_dos && 
                                                 do_id in result.inactive_dos)
                    ) &&
                    (do_id !in dos_to_modify ==> (do_id in result.active_dos && 
                                                  result.active_dos[do_id] == k_objects.active_dos[do_id])
                    )
        // Property: Only the given active DOs <dos_to_modify> is put to the set <result.inactive_dos>
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var new_active_dos := MapRemoveKeys(k_objects.active_dos, dos_to_modify);
    var new_inactive_dos := SetConcat(k_objects.inactive_dos, dos_to_modify);

    k_objects.(active_dos := new_active_dos, inactive_dos := new_inactive_dos)
}

function method SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(
    k_objects:Objects, tds_to_modify:set<TD_ID>, new_pid:Partition_ID
) : (result:Objects)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
    requires forall td_id:: td_id in tds_to_modify ==> td_id in k_objects.inactive_non_hcoded_tds
    requires new_pid != NULL

    ensures AllTDIDs(k_objects) == AllTDIDs(result)
    ensures AllFDIDs(k_objects) == AllFDIDs(result)
    ensures AllDOIDs(k_objects) == AllDOIDs(result)
    ensures AllObjsIDs(k_objects) == AllObjsIDs(result)
    ensures IsValidState_Objects_UniqueObjIDs(result)
        // Property: Object IDs are unchanged
    ensures k_objects.active_fds == result.active_fds
    ensures k_objects.active_dos == result.active_dos
    ensures k_objects.inactive_fds == result.inactive_fds
    ensures k_objects.inactive_dos == result.inactive_dos
    ensures k_objects.hcoded_tds == result.hcoded_tds

    ensures forall td_id :: td_id in k_objects.active_non_hcoded_tds
                ==> td_id in result.active_non_hcoded_tds
    ensures forall td_id :: td_id in result.inactive_non_hcoded_tds
                ==> td_id in k_objects.inactive_non_hcoded_tds
        // Property: Active non-hcoded TDs become more, and inactive ones becomes less
    ensures forall td_id :: td_id in k_objects.inactive_non_hcoded_tds
                ==> (td_id in tds_to_modify ==> (td_id !in result.inactive_non_hcoded_tds && 
                                                 td_id in result.active_non_hcoded_tds &&
                                                 result.active_non_hcoded_tds[td_id] == TD_State(new_pid, TD_Val(map[], map[], map[])))
                    ) &&
                    (td_id !in tds_to_modify ==> (td_id in result.inactive_non_hcoded_tds)
                    )
        // Property: Only the given inactive non-hcoded TDs <tds_to_modify> is put to the set 
        // <result.active_non_hcoded_tds> and cleared
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var map_tds_to_activate := MapCreateFromSet(map[], tds_to_modify, TD_State(new_pid, TD_Val(map[], map[], map[])));
    var new_active_non_hcoded_tds := MapConcat(k_objects.active_non_hcoded_tds, map_tds_to_activate);
    var new_inactive_non_hcoded_tds := SetSubstract(k_objects.inactive_non_hcoded_tds, tds_to_modify);

    k_objects.(active_non_hcoded_tds := new_active_non_hcoded_tds, inactive_non_hcoded_tds := new_inactive_non_hcoded_tds)
}

function method SetPIDsAndClear_InactiveFDs_ToNonNULLPID(
    k_objects:Objects, fds_to_modify:set<FD_ID>, new_pid:Partition_ID
) : (result:Objects)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
    requires forall fd_id:: fd_id in fds_to_modify ==> fd_id in k_objects.inactive_fds
    requires new_pid != NULL

    ensures AllTDIDs(k_objects) == AllTDIDs(result)
    ensures k_objects.active_non_hcoded_tds == result.active_non_hcoded_tds
    ensures k_objects.inactive_non_hcoded_tds == result.inactive_non_hcoded_tds
    ensures k_objects.active_dos == result.active_dos
    ensures k_objects.inactive_dos == result.inactive_dos
    ensures k_objects.hcoded_tds == result.hcoded_tds

    ensures AllFDIDs(k_objects) == AllFDIDs(result)
    ensures AllDOIDs(k_objects) == AllDOIDs(result)
    ensures AllObjsIDs(k_objects) == AllObjsIDs(result)
    ensures IsValidState_Objects_UniqueObjIDs(result)
        // Property: Object IDs are unchanged
    ensures forall fd_id :: fd_id in k_objects.active_fds
                ==> fd_id in result.active_fds
    ensures forall fd_id :: fd_id in result.inactive_fds
                ==> fd_id in k_objects.inactive_fds
        // Property: Active FDs become more, and inactive ones becomes less
    ensures forall fd_id :: fd_id in k_objects.inactive_fds
                ==> (fd_id in fds_to_modify ==> (fd_id !in result.inactive_fds && 
                                                 fd_id in result.active_fds &&
                                                 result.active_fds[fd_id] == FD_State(new_pid, FD_Val("")))
                    ) &&
                    (fd_id !in fds_to_modify ==> (fd_id in result.inactive_fds)
                    )
        // Property: Only the given inactive FDs <fds_to_modify> is put to the set 
        // <result.active_fds> and cleared
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var map_fds_to_activate := MapCreateFromSet(map[], fds_to_modify, FD_State(new_pid, FD_Val("")));
    var new_active_fds := MapConcat(k_objects.active_fds, map_fds_to_activate);
    var new_inactive_fds := SetSubstract(k_objects.inactive_fds, fds_to_modify);

    k_objects.(active_fds := new_active_fds, inactive_fds := new_inactive_fds)
}

function method SetPIDsAndClear_InactiveDOs_ToNonNULLPID(
    k_objects:Objects, dos_to_modify:set<DO_ID>, new_pid:Partition_ID
) : (result:Objects)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
    requires forall do_id:: do_id in dos_to_modify ==> do_id in k_objects.inactive_dos
    requires new_pid != NULL

    ensures AllTDIDs(k_objects) == AllTDIDs(result)
    ensures k_objects.active_non_hcoded_tds == result.active_non_hcoded_tds
    ensures k_objects.inactive_non_hcoded_tds == result.inactive_non_hcoded_tds
    ensures k_objects.active_fds == result.active_fds
    ensures k_objects.inactive_fds == result.inactive_fds
    ensures k_objects.hcoded_tds == result.hcoded_tds
    
    ensures AllFDIDs(k_objects) == AllFDIDs(result)
    ensures AllDOIDs(k_objects) == AllDOIDs(result)
    ensures AllObjsIDs(k_objects) == AllObjsIDs(result)
    ensures IsValidState_Objects_UniqueObjIDs(result)
        // Property: Object IDs are unchanged
    ensures forall do_id :: do_id in k_objects.active_dos
                ==> do_id in result.active_dos
    ensures forall do_id :: do_id in result.inactive_dos
                ==> do_id in k_objects.inactive_dos
        // Property: Active DOs become more, and inactive ones becomes less
    ensures forall do_id :: do_id in k_objects.inactive_dos
                ==> (do_id in dos_to_modify ==> (do_id !in result.inactive_dos && 
                                                 do_id in result.active_dos &&
                                                 result.active_dos[do_id] == DO_State(new_pid, DO_Val("")))
                    ) &&
                    (do_id !in dos_to_modify ==> (do_id in result.inactive_dos)
                    )
        // Property: Only the given inactive DOs <dos_to_modify> is put to the set 
        // <result.active_dos> and cleared
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var map_dos_to_activate := MapCreateFromSet(map[], dos_to_modify, DO_State(new_pid, DO_Val("")));
    var new_active_dos := MapConcat(k_objects.active_dos, map_dos_to_activate);
    var new_inactive_dos := SetSubstract(k_objects.inactive_dos, dos_to_modify);

    k_objects.(active_dos := new_active_dos, inactive_dos := new_inactive_dos)
}

function method SetHCodedTDsPIDs(
    k_objects:Objects, tds_to_modify:set<TD_ID>, new_pid:Partition_ID
) : (result:Objects)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
    requires forall td_id :: td_id in tds_to_modify ==> td_id in k_objects.hcoded_tds

    ensures AllTDIDs(k_objects) == AllTDIDs(result)
    ensures AllFDIDs(k_objects) == AllFDIDs(result)
    ensures AllDOIDs(k_objects) == AllDOIDs(result)
    ensures AllObjsIDs(k_objects) == AllObjsIDs(result)
    ensures MapGetKeys(k_objects.hcoded_tds) == MapGetKeys(result.hcoded_tds)

    ensures k_objects.active_non_hcoded_tds == result.active_non_hcoded_tds
    ensures k_objects.inactive_non_hcoded_tds == result.inactive_non_hcoded_tds
    ensures k_objects.active_fds == result.active_fds
    ensures k_objects.inactive_fds == result.inactive_fds
    ensures k_objects.active_dos == result.active_dos
    ensures k_objects.inactive_dos == result.inactive_dos

    ensures IsValidState_Objects_UniqueObjIDs(result)
        // Property: Object IDs are unchanged
    ensures forall td_id :: td_id in k_objects.hcoded_tds
                ==> (td_id in tds_to_modify ==> (result.hcoded_tds[td_id].pid == new_pid && 
                                                 result.hcoded_tds[td_id].val == k_objects.hcoded_tds[td_id].val)) &&
                    (td_id !in tds_to_modify ==> result.hcoded_tds[td_id] == k_objects.hcoded_tds[td_id])
        // Property: Only the given hcoded TDs <tds_to_modify> are modified
{
    reveal IsValidState_Objects_UniqueObjIDs();
    var new_hcoded_tds := map td_id | td_id in k_objects.hcoded_tds 
                                :: if td_id !in tds_to_modify then 
                                        k_objects.hcoded_tds[td_id] 
                                   else 
                                        TD_State(new_pid, k_objects.hcoded_tds[td_id].val);

    k_objects.(hcoded_tds := new_hcoded_tds)
}

function method DrvDevRead_ReplaceSrcTDWithVal(
    k:State, tds_dst_src:map<TD_ID, TD_ID>
) : (td_id_val_map:map<TD_ID, TD_Val>)
    requires forall td_id :: td_id in tds_dst_src
                ==> tds_dst_src[td_id] in k.objects.active_non_hcoded_tds

    ensures MapGetKeys(td_id_val_map) == MapGetKeys(tds_dst_src)
    ensures forall td_id :: td_id in td_id_val_map
                ==> td_id_val_map[td_id] == k.objects.active_non_hcoded_tds[tds_dst_src[td_id]].val
{
    map td_id | td_id in tds_dst_src :: k.objects.active_non_hcoded_tds[tds_dst_src[td_id]].val
}

function method DrvDevRead_ReplaceSrcFDWithVal(
    k:State, fds_dst_src:map<FD_ID, FD_ID>
) : (fd_id_val_map:map<FD_ID, FD_Val>)
    requires forall fd_id :: fd_id in fds_dst_src
                ==> fds_dst_src[fd_id] in k.objects.active_fds

    ensures MapGetKeys(fd_id_val_map) == MapGetKeys(fds_dst_src)
    ensures forall fd_id :: fd_id in fd_id_val_map
                ==> fd_id_val_map[fd_id] == k.objects.active_fds[fds_dst_src[fd_id]].val
{
    map fd_id | fd_id in fds_dst_src :: k.objects.active_fds[fds_dst_src[fd_id]].val
}

function method DrvDevRead_ReplaceSrcDOWithVal(
    k:State, dos_dst_src:map<DO_ID, DO_ID>
) : (do_id_val_map:map<DO_ID, DO_Val>)
    requires forall do_id :: do_id in dos_dst_src
                ==> dos_dst_src[do_id] in k.objects.active_dos

    ensures MapGetKeys(do_id_val_map) == MapGetKeys(dos_dst_src)
    ensures forall do_id :: do_id in do_id_val_map
                ==> do_id_val_map[do_id] == k.objects.active_dos[dos_dst_src[do_id]].val
{
    map do_id | do_id in dos_dst_src :: k.objects.active_dos[dos_dst_src[do_id]].val
}

predicate ObjStateUnchanged_TD(k_objects:Objects, k'_objects:Objects, td_id:TD_ID)
    requires AllTDIDs(k_objects) == AllTDIDs(k'_objects)
    requires td_id in AllTDIDs(k_objects)
{
    assert td_id in k_objects.active_non_hcoded_tds || td_id in k_objects.inactive_non_hcoded_tds || td_id in k_objects.hcoded_tds;

    if(td_id in k_objects.active_non_hcoded_tds) then
        td_id in k'_objects.active_non_hcoded_tds &&
        k_objects.active_non_hcoded_tds[td_id] == k'_objects.active_non_hcoded_tds[td_id]
    else if (td_id in k_objects.inactive_non_hcoded_tds) then
        td_id in k'_objects.inactive_non_hcoded_tds
    else
        assert td_id in k_objects.hcoded_tds;
        td_id in k'_objects.hcoded_tds &&
        k_objects.hcoded_tds[td_id] == k'_objects.hcoded_tds[td_id]
}

predicate ObjStateUnchanged_FD(k_objects:Objects, k'_objects:Objects, fd_id:FD_ID)
    requires AllFDIDs(k_objects) == AllFDIDs(k'_objects)
    requires fd_id in AllFDIDs(k_objects)
{
    assert fd_id in k_objects.active_fds || fd_id in k_objects.inactive_fds;

    if(fd_id in k_objects.active_fds) then
        fd_id in k'_objects.active_fds &&
        k_objects.active_fds[fd_id] == k'_objects.active_fds[fd_id]
    else
        assert fd_id in k_objects.inactive_fds;
        fd_id in k'_objects.inactive_fds
}

predicate ObjStateUnchanged_DO(k_objects:Objects, k'_objects:Objects, do_id:DO_ID)
    requires AllDOIDs(k_objects) == AllDOIDs(k'_objects)
    requires do_id in AllDOIDs(k_objects)
{
    assert do_id in k_objects.active_dos || do_id in k_objects.inactive_dos;

    if(do_id in k_objects.active_dos) then
        do_id in k'_objects.active_dos &&
        k_objects.active_dos[do_id] == k'_objects.active_dos[do_id]
    else
        assert do_id in k_objects.inactive_dos;
        do_id in k'_objects.inactive_dos
}

function method ActiveObjValue_TD(k_objects:Objects, td_id:TD_ID) : TD_Val
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
        // Requirement: Objects have different internal IDs
    requires td_id in k_objects.active_non_hcoded_tds || td_id in k_objects.hcoded_tds
    requires ObjPID_KObjects(k_objects, td_id.oid) != NULL
{
    if(td_id in k_objects.active_non_hcoded_tds) then
        k_objects.active_non_hcoded_tds[td_id].val
    else
        k_objects.hcoded_tds[td_id].val
}

lemma Lemma_WriteActiveNonHCodedTDsVals_Property_EmptyWriteList(objs:Objects)
    ensures objs == WriteActiveNonHCodedTDsVals(objs, map[])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WriteActiveFDsVals_Property_EmptyWriteList(objs:Objects)
    ensures objs == WriteActiveFDsVals(objs, map[])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_WriteActiveDOsVals_Property_EmptyWriteList(objs:Objects)
    ensures objs == WriteActiveDOsVals(objs, map[])
{
    // Dafny can automatically prove this lemma
}





//******** Utilities for specific operations ********//
function method DrvWrite_ProposedNewState(k:State, 
    td_id_val_map:map<TD_ID, TD_Val>, fd_id_val_map:map<FD_ID, FD_Val>, do_id_val_map:map<DO_ID, DO_Val>
) : (k':State)
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.active_non_hcoded_tds) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.active_fds) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.active_dos)
{
    var t_objs1 := WriteActiveNonHCodedTDsVals(k.objects, td_id_val_map);
    var t_objs2 := WriteActiveFDsVals(t_objs1, fd_id_val_map);
    var new_objects := WriteActiveDOsVals(t_objs2, do_id_val_map);

    State(k.subjects, new_objects, k.pids, k.tds_to_all_states)
}