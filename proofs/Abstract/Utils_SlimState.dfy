include "Syntax.dfy"
include "./utils/Collections.dfy"

predicate {:opaque} IsValidState_Objects_UniqueObjIDs(objs:Objects)
{
    (forall id1 :: id1 in objs.active_non_hcoded_tds
        ==> (FD_ID(id1.oid) !in objs.active_fds &&
             DO_ID(id1.oid) !in objs.active_dos &&
             id1 !in objs.inactive_non_hcoded_tds &&
             FD_ID(id1.oid) !in objs.inactive_fds &&
             DO_ID(id1.oid) !in objs.inactive_dos &&
             id1 !in objs.hcoded_tds
             )
    ) &&
    (forall id1 :: id1 in objs.active_fds
        ==> (DO_ID(id1.oid) !in objs.active_dos &&
             TD_ID(id1.oid) !in objs.inactive_non_hcoded_tds &&
             id1 !in objs.inactive_fds &&
             DO_ID(id1.oid) !in objs.inactive_dos &&
             TD_ID(id1.oid) !in objs.hcoded_tds
             )
    ) &&
    (forall id1 :: id1 in objs.active_dos
        ==> (TD_ID(id1.oid) !in objs.inactive_non_hcoded_tds &&
             FD_ID(id1.oid) !in objs.inactive_fds &&
             id1 !in objs.inactive_dos &&
             TD_ID(id1.oid) !in objs.hcoded_tds
             )
    ) &&
    (forall id1 :: id1 in objs.inactive_non_hcoded_tds
        ==> (FD_ID(id1.oid) !in objs.inactive_fds &&
             DO_ID(id1.oid) !in objs.inactive_dos &&
             id1 !in objs.hcoded_tds
             )
    ) &&
    (forall id1 :: id1 in objs.inactive_fds
        ==> (DO_ID(id1.oid) !in objs.inactive_dos &&
             TD_ID(id1.oid) !in objs.hcoded_tds
            )
    ) &&
    (forall id1 :: id1 in objs.inactive_dos
        ==> (TD_ID(id1.oid) !in objs.hcoded_tds)
    ) &&

    (true)
}

predicate {:opaque} IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(objs:Objects)
{
    (forall id :: id in objs.active_non_hcoded_tds
        ==> objs.active_non_hcoded_tds[id].pid != NULL
    ) &&
    (forall id :: id in objs.active_fds
        ==> objs.active_fds[id].pid != NULL
    ) &&
    (forall id :: id in objs.active_dos
        ==> objs.active_dos[id].pid != NULL
    ) &&

    (true)
}




//******** Fetcher of Helper Variables  ********//
// Return the subject IDs of all drivers
function method AllSubjsIDsInDrvs(k_subjects:Subjects) : set<Subject_ID>
    ensures forall s_id :: s_id in AllSubjsIDsInDrvs(k_subjects)
                <==> Drv_ID(s_id) in k_subjects.drvs
{
    Lemma_SameIDsIffSameInternalIDs();
    (set drv_id, s_id | drv_id in k_subjects.drvs && s_id == drv_id.sid
              :: s_id)
}

// Return the subject IDs of all devices
function method AllSubjsIDsInDevs(k_subjects:Subjects) : set<Subject_ID>
    ensures forall s_id :: s_id in AllSubjsIDsInDevs(k_subjects)
                <==> Dev_ID(s_id) in k_subjects.devs
{
    Lemma_SameIDsIffSameInternalIDs();
    (set dev_id, s_id | dev_id in k_subjects.devs && s_id == dev_id.sid
              :: s_id)
}

// Return the IDs of all subjects
function method AllSubjsIDs(k_subjects:Subjects) : set<Subject_ID>
    ensures forall s_id :: s_id in AllSubjsIDs(k_subjects)
                <==> (Drv_ID(s_id) in k_subjects.drvs) || (Dev_ID(s_id) in k_subjects.devs)
    ensures forall s_id :: s_id in AllSubjsIDs(k_subjects)
                <==> IsSubjID(k_subjects, s_id)
{
    AllSubjsIDsInDrvs(k_subjects) + AllSubjsIDsInDevs(k_subjects)
}

function method AllTDIDs(k_objects:Objects) : (result:set<TD_ID>)
    ensures forall id :: id in result
                <==> id in k_objects.active_non_hcoded_tds || id in k_objects.inactive_non_hcoded_tds || id in k_objects.hcoded_tds
{
    MapGetKeys(k_objects.active_non_hcoded_tds) + k_objects.inactive_non_hcoded_tds + MapGetKeys(k_objects.hcoded_tds)
}

function method AllFDIDs(k_objects:Objects) : (result:set<FD_ID>)
    ensures forall id :: id in result
                <==> id in k_objects.active_fds || id in k_objects.inactive_fds
{
    MapGetKeys(k_objects.active_fds) + k_objects.inactive_fds
}

function method AllDOIDs(k_objects:Objects) : (result:set<DO_ID>)
    ensures forall id :: id in result
                <==> id in k_objects.active_dos || id in k_objects.inactive_dos
{
    MapGetKeys(k_objects.active_dos) + k_objects.inactive_dos
}

// Return the object IDs of all TDs
function method AllObjsIDsInTDs(k_objects:Objects) : set<Object_ID>
    ensures forall o_id :: o_id in AllObjsIDsInTDs(k_objects) 
                <==> (TD_ID(o_id) in AllTDIDs(k_objects))
{
    Lemma_SameIDsIffSameInternalIDs();
    (set td_id, o_id | td_id in AllTDIDs(k_objects) && o_id == td_id.oid
              :: o_id)
}

// Return the object IDs of all FDs
function method AllObjsIDsInFDs(k_objects:Objects) : set<Object_ID>
    ensures forall o_id :: o_id in AllObjsIDsInFDs(k_objects) 
                <==> (FD_ID(o_id) in AllFDIDs(k_objects))
{
    Lemma_SameIDsIffSameInternalIDs();
    (set fd_id, o_id | fd_id in AllFDIDs(k_objects) && o_id == fd_id.oid
              :: o_id)
}

// Return the object IDs of all DOs
function method AllObjsIDsInDOs(k_objects:Objects) : set<Object_ID>
    ensures forall o_id :: o_id in AllObjsIDsInDOs(k_objects) 
                <==> (DO_ID(o_id) in AllDOIDs(k_objects))
{
    Lemma_SameIDsIffSameInternalIDs();
    (set do_id, o_id | do_id in AllDOIDs(k_objects) && o_id == do_id.oid
              :: o_id)
}

// Return the IDs of all objects
function method AllObjsIDs(k_objects:Objects) : set<Object_ID>
{
    AllObjsIDsInTDs(k_objects) + AllObjsIDsInFDs(k_objects) + AllObjsIDsInDOs(k_objects)
}

// [TODO] This function should be removed for a clean proof
function method TDState_FromState(k_objects:Objects): (k_objects_tds:map<TD_ID, TD_State>)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)

    ensures MapGetKeys(k_objects_tds) == AllTDIDs(k_objects)
    ensures forall id :: id in k_objects_tds
                ==> (id in k_objects.active_non_hcoded_tds ==> k_objects_tds[id] == k_objects.active_non_hcoded_tds[id] &&
                     id in k_objects.hcoded_tds ==> k_objects_tds[id] == k_objects.hcoded_tds[id] &&
                     id in k_objects.inactive_non_hcoded_tds ==> k_objects_tds[id] == TD_State(NULL, TD_Val(map[], map[], map[])))
{
    reveal IsValidState_Objects_UniqueObjIDs();
    map id | id in AllTDIDs(k_objects)
            :: if id in k_objects.active_non_hcoded_tds then 
                    k_objects.active_non_hcoded_tds[id] 
               else if id in k_objects.hcoded_tds then
                    k_objects.hcoded_tds[id]
               else
                    // The non-hardcoded TD must be inactive. In this case, we can output an arbitary value for them, 
                    // because their values are not recorded in the state. We must return their PID as NULL.
                    TD_State(NULL, TD_Val(map[], map[], map[]))
}




//******** Subjects/Objects ID  ********//
function method IsDrvID_SlimState(k_subjects:Subjects, drv_id:Drv_ID) : bool
{
    drv_id in k_subjects.drvs
}

function method IsDevID_SlimState(k_subjects:Subjects, dev_id:Dev_ID) : bool
{
    dev_id in k_subjects.devs
}

function method IDToDev_SlimState(k_subjects:Subjects, dev_id:Dev_ID) : Dev_State
    requires dev_id in k_subjects.devs
{
    k_subjects.devs[dev_id]
}

function method IsSubjID(k_subjects:Subjects, s_id:Subject_ID) : bool
    ensures IsSubjID(k_subjects, s_id) 
                <==> (Drv_ID(s_id) in k_subjects.drvs || Dev_ID(s_id) in k_subjects.devs)
{
    Drv_ID(s_id) in k_subjects.drvs || Dev_ID(s_id) in k_subjects.devs
}

function method IsObjID(k_objects:Objects, o_id:Object_ID) : bool
{
    o_id in AllObjsIDs(k_objects)
}




//******** Objects Ownership ********//
// Does the subject (id == <s_id> own the object (id == <o_id>)
function method DoOwnObj_SlimState(k_subjects:Subjects, s_id:Subject_ID, o_id:Object_ID) : bool
    requires IsSubjID(k_subjects, s_id)
{
    if(Drv_ID(s_id) in k_subjects.drvs) then
        (TD_ID(o_id) in k_subjects.drvs[Drv_ID(s_id)].td_ids) ||
        (FD_ID(o_id) in k_subjects.drvs[Drv_ID(s_id)].fd_ids) ||
        (DO_ID(o_id) in k_subjects.drvs[Drv_ID(s_id)].do_ids)
    else
        (TD_ID(o_id) in k_subjects.devs[Dev_ID(s_id)].td_ids) ||
        (FD_ID(o_id) in k_subjects.devs[Dev_ID(s_id)].fd_ids) ||
        (DO_ID(o_id) in k_subjects.devs[Dev_ID(s_id)].do_ids)
}

function method OwnedTDs_SlimState(k_subjects:Subjects, s_id:Subject_ID) : set<TD_ID>
    requires IsSubjID(k_subjects, s_id)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k_subjects.drvs) && (Dev_ID(dev_sid) in k_subjects.devs)
         ==> (drv_sid != dev_sid)
    ensures Drv_ID(s_id) in k_subjects.drvs
                ==> OwnedTDs_SlimState(k_subjects, s_id) == k_subjects.drvs[Drv_ID(s_id)].td_ids
    ensures Dev_ID(s_id) in k_subjects.devs
                ==> OwnedTDs_SlimState(k_subjects, s_id) == k_subjects.devs[Dev_ID(s_id)].td_ids

{
    if(Drv_ID(s_id) in k_subjects.drvs) then
        (k_subjects.drvs[Drv_ID(s_id)].td_ids)
    else
        (k_subjects.devs[Dev_ID(s_id)].td_ids)
}

function method OwnedFDs_SlimState(k_subjects:Subjects, s_id:Subject_ID) : set<FD_ID>
    requires IsSubjID(k_subjects, s_id)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k_subjects.drvs) && (Dev_ID(dev_sid) in k_subjects.devs)
         ==> (drv_sid != dev_sid)
    ensures Drv_ID(s_id) in k_subjects.drvs
                ==> OwnedFDs_SlimState(k_subjects, s_id) == k_subjects.drvs[Drv_ID(s_id)].fd_ids
    ensures Dev_ID(s_id) in k_subjects.devs
                ==> OwnedFDs_SlimState(k_subjects, s_id) == k_subjects.devs[Dev_ID(s_id)].fd_ids

{
    if(Drv_ID(s_id) in k_subjects.drvs) then
        (k_subjects.drvs[Drv_ID(s_id)].fd_ids)
    else
        (k_subjects.devs[Dev_ID(s_id)].fd_ids)
}

function method OwnedDOs_SlimState(k_subjects:Subjects, s_id:Subject_ID) : set<DO_ID>
    requires IsSubjID(k_subjects, s_id)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k_subjects.drvs) && (Dev_ID(dev_sid) in k_subjects.devs)
         ==> (drv_sid != dev_sid)
    ensures Drv_ID(s_id) in k_subjects.drvs
                ==> OwnedDOs_SlimState(k_subjects, s_id) == k_subjects.drvs[Drv_ID(s_id)].do_ids
    ensures Dev_ID(s_id) in k_subjects.devs
                ==> OwnedDOs_SlimState(k_subjects, s_id) == k_subjects.devs[Dev_ID(s_id)].do_ids
{
    if(Drv_ID(s_id) in k_subjects.drvs) then
        (k_subjects.drvs[Drv_ID(s_id)].do_ids)
    else
        (k_subjects.devs[Dev_ID(s_id)].do_ids)
}




//******** Partition ID  ********//
function method BuildMap_ObjIDsToPIDs(k_objects:Objects) : (result:map<Object_ID, Partition_ID>)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
        // Requirement: Objects have different internal IDs
    
    ensures MapGetKeys(result) == AllObjsIDs(k_objects)
    ensures forall o_id :: o_id in AllObjsIDs(k_objects)
                ==> (TD_ID(o_id) in k_objects.active_non_hcoded_tds ==> result[o_id] == k_objects.active_non_hcoded_tds[TD_ID(o_id)].pid) &&
                    (FD_ID(o_id) in k_objects.active_fds ==> result[o_id] == k_objects.active_fds[FD_ID(o_id)].pid) &&
                    (DO_ID(o_id) in k_objects.active_dos ==> result[o_id] == k_objects.active_dos[DO_ID(o_id)].pid) &&
                    (TD_ID(o_id) in k_objects.inactive_non_hcoded_tds ==> result[o_id] == NULL) &&
                    (FD_ID(o_id) in k_objects.inactive_fds ==> result[o_id] == NULL) &&
                    (DO_ID(o_id) in k_objects.inactive_dos ==> result[o_id] == NULL) &&
                    (TD_ID(o_id) in k_objects.hcoded_tds ==> result[o_id] == k_objects.hcoded_tds[TD_ID(o_id)].pid)
{
    reveal IsValidState_Objects_UniqueObjIDs();
    MapConcat(
        MapConcat(BuildMap_ObjIDsToPIDs_ForTDs(k_objects), BuildMap_ObjIDsToPIDs_ForFDs(k_objects)),
        BuildMap_ObjIDsToPIDs_ForDOs(k_objects)
    )
}

function method ObjPID_SlimState(
    k_objs_pids:map<Object_ID, Partition_ID>, o_id:Object_ID
) : Partition_ID
    requires o_id in k_objs_pids
{
    k_objs_pids[o_id]
}

function method SubjPID_SlimState(k_subjects:Subjects, s_id:Subject_ID) : Partition_ID
    requires IsSubjID(k_subjects, s_id)
{
    if Drv_ID(s_id) in k_subjects.drvs then
        k_subjects.drvs[Drv_ID(s_id)].pid
    else
        k_subjects.devs[Dev_ID(s_id)].pid
}

function method SubjPID_DevID_SlimState(k_subjects:Subjects, dev_id:Dev_ID) : Partition_ID
    requires IsDevID_SlimState(k_subjects, dev_id)
{
    k_subjects.devs[dev_id].pid
}




//******** Active/Inactive Subjects/Objects  ********//
// Return all active subjects in the current state <k>
function method AllActiveSubjs_SlimState(k_subjects:Subjects) : set<Subject_ID>
{
    set s_id | s_id in AllSubjsIDs(k_subjects) && SubjPID_SlimState(k_subjects, s_id) != NULL :: s_id 
}

// Return all active objects in the current state <k>
function method AllActiveObjs_SlimState(k_objects:Objects) : (result:set<Object_ID>)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
        // Requirement: Objects have different internal IDs

    ensures forall td_id :: td_id in k_objects.active_non_hcoded_tds && k_objects.active_non_hcoded_tds[td_id].pid != NULL
                ==> td_id.oid in result
    ensures forall fd_id :: fd_id in k_objects.active_fds && k_objects.active_fds[fd_id].pid != NULL
                ==> fd_id.oid in result
    ensures forall do_id :: do_id in k_objects.active_dos && k_objects.active_dos[do_id].pid != NULL
                ==> do_id.oid in result
    ensures forall td_id :: td_id in k_objects.hcoded_tds && k_objects.hcoded_tds[td_id].pid != NULL
                ==> td_id.oid in result
        // Property 1: All active objects are in the result
    ensures forall o_id :: o_id in result
                ==> (TD_ID(o_id) in k_objects.active_non_hcoded_tds || FD_ID(o_id) in k_objects.active_fds || 
                     DO_ID(o_id) in k_objects.active_dos || TD_ID(o_id) in k_objects.hcoded_tds)
    ensures forall o_id :: o_id in result
                ==> (TD_ID(o_id) in k_objects.active_non_hcoded_tds ==> k_objects.active_non_hcoded_tds[TD_ID(o_id)].pid != NULL) &&
                    (FD_ID(o_id) in k_objects.active_fds ==> k_objects.active_fds[FD_ID(o_id)].pid != NULL) &&
                    (DO_ID(o_id) in k_objects.active_dos ==> k_objects.active_dos[DO_ID(o_id)].pid != NULL) &&
                    (TD_ID(o_id) in k_objects.hcoded_tds ==> k_objects.hcoded_tds[TD_ID(o_id)].pid != NULL)
        // Property 2: All objects in the result are active
{
    Lemma_AllActiveObjs_SlimState_Property(k_objects);
    set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id 
}

function method AllActiveDrvs_SlimState(k_subjects:Subjects) : set<Drv_ID>
    ensures forall drv_id :: drv_id in AllActiveDrvs_SlimState(k_subjects) 
                ==> drv_id.sid in AllActiveSubjs_SlimState(k_subjects)
    ensures forall drv_id :: drv_id in AllActiveDrvs_SlimState(k_subjects) 
                ==> IsDrvID_SlimState(k_subjects, drv_id)
{
    set drv_id | drv_id in k_subjects.drvs && SubjPID_SlimState(k_subjects, drv_id.sid) != NULL :: drv_id 
}

function method AllActiveDevs_SlimState(k_subjects:Subjects) : set<Dev_ID>
    ensures forall dev_id :: dev_id in AllActiveDevs_SlimState(k_subjects) 
                ==> dev_id.sid in AllActiveSubjs_SlimState(k_subjects)
    ensures forall dev_id :: dev_id in AllActiveDevs_SlimState(k_subjects) 
                ==> IsDevID_SlimState(k_subjects, dev_id)
{
    set dev_id | dev_id in k_subjects.devs && SubjPID_SlimState(k_subjects, dev_id.sid) != NULL :: dev_id 
}

function method AllActiveTDs_SlimState(k_objects:Objects) : (result:set<TD_ID>)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
        // Requirement: Objects have different internal IDs

    ensures result <= AllTDIDs(k_objects)
    ensures forall td_id :: td_id in result
                <==> td_id in AllTDIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), td_id.oid) != NULL
{
    var objs_pids := BuildMap_ObjIDsToPIDs(k_objects);
    var all_td_ids := AllTDIDs(k_objects);

    set td_id | td_id in all_td_ids && ObjPID_SlimState(objs_pids, td_id.oid) != NULL :: td_id 
}

function method AllActiveFDs_SlimState(k_objects:Objects) : (result:set<FD_ID>)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
        // Requirement: Objects have different internal IDs

    ensures result <= AllFDIDs(k_objects)
    ensures forall fd_id :: fd_id in result
                <==> fd_id in AllFDIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), fd_id.oid) != NULL
{
    var objs_pids := BuildMap_ObjIDsToPIDs(k_objects);
    var all_fd_ids := AllFDIDs(k_objects);

    set fd_id | fd_id in all_fd_ids && ObjPID_SlimState(objs_pids, fd_id.oid) != NULL :: fd_id 
}

function method AllActiveDOs_SlimState(k_objects:Objects) : (result:set<DO_ID>)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
        // Requirement: Objects have different internal IDs

    ensures result <= AllDOIDs(k_objects)
    ensures forall do_id :: do_id in result
                <==> do_id in AllDOIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), do_id.oid) != NULL
{
    var objs_pids := BuildMap_ObjIDsToPIDs(k_objects);
    var all_do_ids := AllDOIDs(k_objects);

    set do_id | do_id in all_do_ids && ObjPID_SlimState(objs_pids, do_id.oid) != NULL :: do_id 
}

function method ActiveTDsState_SlimState(k_objects:Objects) : (result:map<TD_ID, TD_Val>)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
        // Requirement: Objects have different internal IDs

    ensures MapGetKeys(result) == AllActiveTDs_SlimState(k_objects)
        // Property: The result includes active TDs only
    ensures forall td_id :: td_id in result
                ==> td_id in k_objects.active_non_hcoded_tds || td_id in k_objects.hcoded_tds
    ensures forall td_id :: td_id in result
                ==> (td_id in k_objects.active_non_hcoded_tds ==> result[td_id] == k_objects.active_non_hcoded_tds[td_id].val) &&
                    (td_id in k_objects.hcoded_tds ==> result[td_id] == k_objects.hcoded_tds[td_id].val)
        // Property: The values of active TDs are from <k_objects>
{
    assert forall td_id :: td_id in AllActiveTDs_SlimState(k_objects)
                ==> td_id in k_objects.active_non_hcoded_tds || td_id in k_objects.hcoded_tds;

    var m1 := map td_id | td_id in k_objects.active_non_hcoded_tds && k_objects.active_non_hcoded_tds[td_id].pid != NULL
              :: k_objects.active_non_hcoded_tds[td_id].val;
    var m2 := map td_id | td_id in k_objects.hcoded_tds && k_objects.hcoded_tds[td_id].pid != NULL
              :: k_objects.hcoded_tds[td_id].val;

    MapConcat(m1, m2)
}



//******** Private Functions ********//
function method BuildMap_ObjIDsToPIDs_ForTDs(k_objects:Objects) : (result:map<Object_ID, Partition_ID>)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)

    ensures MapGetKeys(result) == AllObjsIDsInTDs(k_objects)
    ensures forall o_id :: o_id in result
                ==> TD_ID(o_id) in k_objects.active_non_hcoded_tds || TD_ID(o_id) in k_objects.inactive_non_hcoded_tds || TD_ID(o_id) in k_objects.hcoded_tds
        // Property: The IDs in the result is correct
    ensures forall o_id :: o_id in result
                ==> ((TD_ID(o_id) in k_objects.active_non_hcoded_tds ==> result[o_id] == k_objects.active_non_hcoded_tds[TD_ID(o_id)].pid) &&
                     (TD_ID(o_id) in k_objects.hcoded_tds ==> result[o_id] == k_objects.hcoded_tds[TD_ID(o_id)].pid) &&
                     (TD_ID(o_id) in k_objects.inactive_non_hcoded_tds ==> result[o_id] == NULL))
{
    reveal IsValidState_Objects_UniqueObjIDs();
    map o_id | o_id in AllObjsIDsInTDs(k_objects)
            :: if TD_ID(o_id) in k_objects.active_non_hcoded_tds then 
                    k_objects.active_non_hcoded_tds[TD_ID(o_id)].pid 
               else if TD_ID(o_id) in k_objects.hcoded_tds then
                    k_objects.hcoded_tds[TD_ID(o_id)].pid
               else
                    NULL
}

function method BuildMap_ObjIDsToPIDs_ForFDs(k_objects:Objects) : (result:map<Object_ID, Partition_ID>)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)

    ensures MapGetKeys(result) == AllObjsIDsInFDs(k_objects)
    ensures forall o_id :: o_id in result
                ==> FD_ID(o_id) in k_objects.active_fds || FD_ID(o_id) in k_objects.inactive_fds
        // Property: The IDs in the result is correct
    ensures forall o_id :: o_id in result
                ==> ((FD_ID(o_id) in k_objects.active_fds ==> result[o_id] == k_objects.active_fds[FD_ID(o_id)].pid) &&
                     (FD_ID(o_id) in k_objects.inactive_fds ==> result[o_id] == NULL))
{
    reveal IsValidState_Objects_UniqueObjIDs();
    map o_id | o_id in AllObjsIDsInFDs(k_objects)
            :: if FD_ID(o_id) in k_objects.active_fds then k_objects.active_fds[FD_ID(o_id)].pid else NULL
}

function method BuildMap_ObjIDsToPIDs_ForDOs(k_objects:Objects) : (result:map<Object_ID, Partition_ID>)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)

    ensures MapGetKeys(result) == AllObjsIDsInDOs(k_objects)
    ensures forall o_id :: o_id in result
                ==> DO_ID(o_id) in k_objects.active_dos || DO_ID(o_id) in k_objects.inactive_dos
        // Property: The IDs in the result is correct
    ensures forall o_id :: o_id in result
                ==> ((DO_ID(o_id) in k_objects.active_dos ==> result[o_id] == k_objects.active_dos[DO_ID(o_id)].pid) &&
                     (DO_ID(o_id) in k_objects.inactive_dos ==> result[o_id] == NULL))
{
    reveal IsValidState_Objects_UniqueObjIDs();
    map o_id | o_id in AllObjsIDsInDOs(k_objects)
            :: if DO_ID(o_id) in k_objects.active_dos then k_objects.active_dos[DO_ID(o_id)].pid else NULL
}




//******** Utility Lemmas  ********//
// Lemma: TDs returned by AllActiveTDs_SlimState are also in 
// AllActiveObjs_SlimState(k_objects)
lemma Lemma_AllActiveTDs_SlimState_TDsAreAlsoActiveObjs(k_objects:Objects)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
        // Requirement: Objects have different internal IDs

    ensures forall td_id :: td_id in AllActiveTDs_SlimState(k_objects)
                ==> td_id.oid in AllActiveObjs_SlimState(k_objects)
    ensures forall td_id :: td_id in AllActiveTDs_SlimState(k_objects) 
                <==> td_id in AllTDIDs(k_objects) && td_id.oid in AllActiveObjs_SlimState(k_objects)
{
    assert forall td_id :: td_id in AllActiveTDs_SlimState(k_objects) 
                <==> td_id in AllTDIDs(k_objects) && td_id.oid in AllActiveObjs_SlimState(k_objects);
}

lemma Lemma_SameSubjectsOwnSameObjectsInSuccessiveStates(k_subjects:Subjects, k'_subjects:Subjects)
    requires MapGetKeys<Drv_ID, Drv_State>(k'_subjects.drvs) == MapGetKeys<Drv_ID, Drv_State>(k_subjects.drvs)
    requires MapGetKeys<Dev_ID, Dev_State>(k'_subjects.devs) == MapGetKeys<Dev_ID, Dev_State>(k_subjects.devs)
    requires forall drv_id :: drv_id in k_subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k_subjects.drvs[drv_id].td_ids) &&
                    (k'_subjects.drvs[drv_id].fd_ids == k_subjects.drvs[drv_id].fd_ids) &&
                    (k'_subjects.drvs[drv_id].do_ids == k_subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].td_ids == k_subjects.devs[dev_id].td_ids) &&
                    (k'_subjects.devs[dev_id].fd_ids == k_subjects.devs[dev_id].fd_ids) &&
                    (k'_subjects.devs[dev_id].do_ids == k_subjects.devs[dev_id].do_ids)

    ensures forall s_id, o_id :: (Drv_ID(s_id) in k_subjects.drvs || Dev_ID(s_id) in k_subjects.devs) &&
                    DoOwnObj_SlimState(k_subjects, s_id, o_id)
                ==> DoOwnObj_SlimState(k'_subjects, s_id, o_id)
{
    // Dafny can automatically prove this lemma
}

// Drv_ID/Dev_ID/TD_ID/FD_ID/DO_ID are same, iff internal Subject_ID/Object_ID is same
lemma Lemma_SameIDsIffSameInternalIDs()
    ensures forall drv_id1:Drv_ID, drv_id2:Drv_ID :: drv_id1 == drv_id2
               <==> drv_id1.sid == drv_id2.sid
    ensures forall dev_id1:Dev_ID, dev_id2:Dev_ID :: dev_id1 == dev_id2
               <==> dev_id1.sid == dev_id2.sid

    ensures forall td_id1:TD_ID, td_id2:TD_ID :: td_id1 == td_id2
               <==> td_id1.oid == td_id2.oid
    ensures forall fd_id1:FD_ID, fd_id2:FD_ID :: fd_id1 == fd_id2
               <==> fd_id1.oid == fd_id2.oid
    ensures forall do_id1:DO_ID, do_id2:DO_ID :: do_id1 == do_id2
               <==> do_id1.oid == do_id2.oid
{
    assert forall drv_id1:Drv_ID, drv_id2:Drv_ID :: drv_id1 == drv_id2
               <==> drv_id1.sid == drv_id2.sid;
    assert forall dev_id1:Dev_ID, dev_id2:Dev_ID :: dev_id1 == dev_id2
               <==> dev_id1.sid == dev_id2.sid;

    assert forall td_id1:TD_ID, td_id2:TD_ID :: td_id1 == td_id2
               <==> td_id1.oid == td_id2.oid;
    assert forall fd_id1:FD_ID, fd_id2:FD_ID :: fd_id1 == fd_id2
               <==> fd_id1.oid == fd_id2.oid;
    assert forall do_id1:DO_ID, do_id2:DO_ID :: do_id1 == do_id2
               <==> do_id1.oid == do_id2.oid;
}




//******** Private Lemmas  ********//
lemma Lemma_AllActiveObjs_SlimState_Property(k_objects:Objects)
    requires IsValidState_Objects_UniqueObjIDs(k_objects)
        // Requirement: Objects have different internal IDs

    ensures forall td_id :: td_id in k_objects.active_non_hcoded_tds && k_objects.active_non_hcoded_tds[td_id].pid != NULL
                ==> td_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
    ensures forall td_id :: td_id in k_objects.hcoded_tds && k_objects.hcoded_tds[td_id].pid != NULL
                ==> td_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
    ensures forall fd_id :: fd_id in k_objects.active_fds && k_objects.active_fds[fd_id].pid != NULL
                ==> fd_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
    ensures forall do_id :: do_id in k_objects.active_dos && k_objects.active_dos[do_id].pid != NULL
                ==> do_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
{
    forall td_id | td_id in k_objects.active_non_hcoded_tds && k_objects.active_non_hcoded_tds[td_id].pid != NULL
        ensures td_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
    {
        var objs_pids := BuildMap_ObjIDsToPIDs(k_objects);

        assert td_id.oid in objs_pids;
        assert objs_pids[td_id.oid] == k_objects.active_non_hcoded_tds[td_id].pid;
    }

    forall td_id | td_id in k_objects.hcoded_tds && k_objects.hcoded_tds[td_id].pid != NULL
        ensures td_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
    {
        var objs_pids := BuildMap_ObjIDsToPIDs(k_objects);

        assert td_id.oid in objs_pids;
        assert objs_pids[td_id.oid] == k_objects.hcoded_tds[td_id].pid;
    }

    forall fd_id | fd_id in k_objects.active_fds && k_objects.active_fds[fd_id].pid != NULL
        ensures fd_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
    {
        var objs_pids := BuildMap_ObjIDsToPIDs(k_objects);

        assert fd_id.oid in objs_pids;
        assert objs_pids[fd_id.oid] == k_objects.active_fds[fd_id].pid;
    }

    forall do_id | do_id in k_objects.active_dos && k_objects.active_dos[do_id].pid != NULL
        ensures do_id.oid in (set o_id | o_id in AllObjsIDs(k_objects) && ObjPID_SlimState(BuildMap_ObjIDsToPIDs(k_objects), o_id) != NULL :: o_id)
    {
        var objs_pids := BuildMap_ObjIDsToPIDs(k_objects);

        assert do_id.oid in objs_pids;
        assert objs_pids[do_id.oid] == k_objects.active_dos[do_id].pid;
    }
}