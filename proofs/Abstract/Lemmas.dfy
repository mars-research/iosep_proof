include "Syntax.dfy"
include "Utils.dfy"
include "HCodedTD_Ops.dfy"

lemma AModeIsEitherROrW()
    ensures forall amode:AMode :: amode == R || amode == W
{
    forall a:AMode
        ensures a == R || a == W
    {
        if(a.R?)
        {}
        else
        { assert a.W?;}
    }
}

// Lemma: Any requested access modes and permissions are subset of {R,W}
lemma AllReqAModesPermsSubsetOfRW()
    ensures forall perms:set<AMode> :: perms <= {R,W}
    ensures forall perms:set<AMode> :: perms == {} || perms == {R} || perms == {W} || perms == {R,W}
{
    AModeIsEitherROrW();
}

lemma AllReqNonEmptyAModesMustContainROrW()
    ensures forall perms:set<AMode> :: perms != {} 
                ==> R in perms || W in perms
{
    AllReqAModesPermsSubsetOfRW();
}

lemma IfAModesContainROrWThenNotEmpty()
    ensures forall perms:set<AMode> :: R in perms || W in perms
                ==> perms != {}
{
    AllReqAModesPermsSubsetOfRW();
}

lemma Lemma_EmptyAModesIsNoRAndNoW(amodes:set<AMode>)
    ensures amodes == {} 
            <==> R !in amodes && W !in amodes
{
    AllReqAModesPermsSubsetOfRW();
}

lemma Lemma_SameAllSubjsIDsBetweenStates(k:State, k'_subjects:Subjects)
    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)
     
    ensures AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)
{
    Lemma_SameIDsIffSameInternalIDs();
}

lemma Lemma_AllTDFDDOIDsAreInObjIDs(k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>)
    requires td_ids <= AllTDIDs(k.objects)
    requires fd_ids <= AllFDIDs(k.objects)
    requires do_ids <= AllDOIDs(k.objects)

    ensures (forall id :: id in td_ids ==> id.oid in AllObjsIDs(k.objects)) &&
            (forall id :: id in fd_ids ==> id.oid in AllObjsIDs(k.objects)) &&
            (forall id :: id in do_ids ==> id.oid in AllObjsIDs(k.objects))
{
    Lemma_SameIDsIffSameInternalIDs();
}

lemma Lemma_SameAllObjsIDsBetweenStates(k:State, k'_objects:Objects)
    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)
     
    ensures AllObjsIDs(k'_objects) == AllObjsIDs(k.objects)
{
    Lemma_SameIDsIffSameInternalIDs();
}

lemma Lemma_TDFDDOIDsInStateAlsoHasObjIDsInState(k:State, td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>)
    requires forall td_id :: td_id in td_ids ==> td_id in AllTDIDs(k.objects)
    requires forall fd_id :: fd_id in fd_ids ==> fd_id in AllFDIDs(k.objects)
    requires forall do_id :: do_id in do_ids ==> do_id in AllDOIDs(k.objects)

    ensures TDIDsToObjIDs(td_ids) <= AllObjsIDs(k.objects)
    ensures FDIDsToObjIDs(fd_ids) <= AllObjsIDs(k.objects)
    ensures DOIDsToObjIDs(do_ids) <= AllObjsIDs(k.objects)
    ensures TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids) <= AllObjsIDs(k.objects)
{
    // Dafny can automatically prove this lemma.
}

lemma Lemma_SameSubjObjIDsInSuccessiveStates(k:State, k':State)
    requires (forall s_id :: 
                (Drv_ID(s_id) in k.subjects.drvs <==> Drv_ID(s_id) in k'.subjects.drvs) &&
                (Dev_ID(s_id) in k.subjects.devs <==> Dev_ID(s_id) in k'.subjects.devs))
    requires forall td_id :: td_id in AllTDIDs(k.objects) <==> td_id in AllTDIDs(k'.objects)
    requires forall fd_id :: fd_id in AllFDIDs(k.objects) <==> fd_id in AllFDIDs(k'.objects)
    requires forall do_id :: do_id in AllDOIDs(k.objects) <==> do_id in AllDOIDs(k'.objects)
    requires |AllTDIDs(k.objects)| + |AllFDIDs(k.objects)| + 
            |AllDOIDs(k.objects)| > 0

    ensures AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects)
    ensures AllObjsIDs(k'.objects) == AllObjsIDs(k.objects)
    ensures AllTDIDs(k'.objects) == AllTDIDs(k.objects)
    ensures AllFDIDs(k'.objects) == AllFDIDs(k.objects)
    ensures AllDOIDs(k'.objects) == AllDOIDs(k.objects)
    ensures (forall dev_id :: IsDevID(k', dev_id) == IsDevID(k, dev_id))
    ensures (forall drv_id :: IsDrvID(k', drv_id) == IsDrvID(k, drv_id))
    ensures |AllTDIDs(k'.objects)| + |AllFDIDs(k'.objects)| + 
            |AllDOIDs(k'.objects)| > 0
{
    assert forall dev_id :: IsDevID(k, dev_id) <==> Dev_ID(dev_id.sid) in k.subjects.devs;
    assert forall drv_id :: IsDrvID(k, drv_id) <==> Drv_ID(drv_id.sid) in k.subjects.drvs;

    assert AllTDIDs(k.objects) == AllTDIDs(k'.objects);
    assert |AllTDIDs(k.objects)| == |AllTDIDs(k'.objects)|;
}

lemma Lemma_ObjsInSubjsAreAlsoInState(k:State)
    requires forall drv_id, td_id :: 
                drv_id in k.subjects.drvs && td_id in k.subjects.drvs[drv_id].td_ids
                ==> td_id in AllTDIDs(k.objects)
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)
    requires forall drv_id, fd_id :: 
                drv_id in k.subjects.drvs && fd_id in k.subjects.drvs[drv_id].fd_ids
                ==> fd_id in AllFDIDs(k.objects)
    requires forall dev_id, fd_id :: 
                dev_id in k.subjects.devs && fd_id in k.subjects.devs[dev_id].fd_ids
                ==> fd_id in AllFDIDs(k.objects)
    requires forall drv_id, do_id :: 
                drv_id in k.subjects.drvs && do_id in k.subjects.drvs[drv_id].do_ids
                ==> do_id in AllDOIDs(k.objects) 
    requires forall dev_id, do_id :: 
                dev_id in k.subjects.devs && do_id in k.subjects.devs[dev_id].do_ids
                ==> do_id in AllDOIDs(k.objects)

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id)
                ==> o_id in AllObjsIDs(k.objects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewK_FulfillCondition28(k:State, k':State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
        
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)

    requires MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)
    requires AllTDIDs(k'.objects) == AllTDIDs(k.objects)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k'.subjects.devs[dev_id].hcoded_td_id in k'.objects.hcoded_tds

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (MapGetKeys(HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k.subjects, k.objects), dev_id).trans_params_tds) <= 
                        IDToDev(k, dev_id).td_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k.subjects, k.objects), dev_id).trans_params_fds) <= 
                        IDToDev(k, dev_id).fd_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k.subjects, k.objects), dev_id).trans_params_dos) <= 
                        IDToDev(k, dev_id).do_ids)
        // Requirement: k fulfills Condition 2.8
    requires BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects) == BuildMap_DevsToHCodedTDVals(k.subjects, k.objects)

    ensures forall dev_id :: dev_id in k'.subjects.devs
                ==> (MapGetKeys(HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects), dev_id).trans_params_tds) <= 
                        IDToDev(k', dev_id).td_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects), dev_id).trans_params_fds) <= 
                        IDToDev(k', dev_id).fd_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects), dev_id).trans_params_dos) <= 
                        IDToDev(k', dev_id).do_ids)
        // Property: k' fulfills Condition 2.8
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewK_FulfillCondition27(k:State, k':State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)

    requires MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)
    requires AllTDIDs(k'.objects) == AllTDIDs(k.objects)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k'.subjects.devs[dev_id].hcoded_td_id in k'.objects.hcoded_tds

    requires forall dev_id, td_id :: dev_id in k.subjects.devs &&
                        td_id in HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k.subjects, k.objects), dev_id).trans_params_tds
                ==> td_id !in AllHCodedTDIDs(k.subjects)
        // Requirement: k fulfills Condition 2.8
    requires BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects) == BuildMap_DevsToHCodedTDVals(k.subjects, k.objects)

    ensures forall dev_id, td_id :: dev_id in k'.subjects.devs &&
                        td_id in HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects), dev_id).trans_params_tds
                ==> td_id !in AllHCodedTDIDs(k'.subjects)
        // Property: k' fulfills Condition 2.7
{
    assert forall dev_id, td_id :: 
                dev_id in k'.subjects.devs && td_id in k'.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k'.objects);

    forall dev_id, td_id | dev_id in k'.subjects.devs &&
                        td_id in HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects), dev_id).trans_params_tds
        ensures td_id !in AllHCodedTDIDs(k'.subjects)
    {
        assert dev_id in k.subjects.devs;
        assert td_id in HCodedTDValOfDev(BuildMap_DevsToHCodedTDVals(k.subjects, k.objects), dev_id).trans_params_tds;
        assert td_id !in AllHCodedTDIDs(k.subjects);
    }
}

lemma Lemma_SameSubjObjPIDsIfSubjPIDsAreUnchanged(k:State, k':State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
        // Requirement: Objects have different internal IDs

    requires MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)
    requires MapGetKeys(k'.objects.active_non_hcoded_tds) == MapGetKeys(k.objects.active_non_hcoded_tds)
    requires MapGetKeys(k'.objects.active_fds) == MapGetKeys(k.objects.active_fds)
    requires MapGetKeys(k'.objects.active_dos) == MapGetKeys(k.objects.active_dos)
    requires k'.objects.inactive_non_hcoded_tds == k.objects.inactive_non_hcoded_tds
    requires k'.objects.inactive_fds == k.objects.inactive_fds
    requires k'.objects.inactive_dos == k.objects.inactive_dos
    requires MapGetKeys(k'.objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)

    requires forall drv_id :: drv_id in k.subjects.drvs
                ==> (k'.subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                    (k'.subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                    (k'.subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
        // Requirement: Ownership is unchanged
    requires forall drv_id :: drv_id in k.subjects.drvs
                ==> k.subjects.drvs[drv_id].pid == k'.subjects.drvs[drv_id].pid
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].pid == k'.subjects.devs[dev_id].pid
        // Requirement: PIDs of subjects are unchanged
    requires forall td_id :: td_id in k.objects.active_non_hcoded_tds
                ==> k'.objects.active_non_hcoded_tds[td_id].pid == k.objects.active_non_hcoded_tds[td_id].pid
    requires forall fd_id :: fd_id in k.objects.active_fds
                ==> k'.objects.active_fds[fd_id].pid == k.objects.active_fds[fd_id].pid
    requires forall do_id :: do_id in k.objects.active_dos
                ==> k'.objects.active_dos[do_id].pid == k.objects.active_dos[do_id].pid
    requires forall td_id :: td_id in k.objects.hcoded_tds
                ==> k'.objects.hcoded_tds[td_id].pid == k.objects.hcoded_tds[td_id].pid
        // Requirement: PIDs of objects are unchanged

    ensures IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Propertiesw needed by the following property
    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects)
                ==> SubjPID(k, s_id) == SubjPID(k', s_id)
    ensures forall o_id :: o_id in AllObjsIDs(k.objects)
                ==> ObjPID(k, o_id) == ObjPID(k', o_id)

    ensures AllActiveSubjs(k) == AllActiveSubjs(k')
    ensures AllActiveDevs(k) == AllActiveDevs(k')
    ensures AllActiveObjs(k) == AllActiveObjs(k')
{
    reveal IsValidState_Objects_UniqueObjIDs();
    
    Lemma_SameAllSubjsIDsBetweenStates(k, k'.subjects);
    Lemma_SameAllObjsIDsBetweenStates(k, k'.objects);

    assert(forall s_id :: Drv_ID(s_id) in k.subjects.drvs
            ==> SubjPID(k, s_id) == SubjPID(k', s_id)); 
    assert(forall s_id :: Dev_ID(s_id) in k.subjects.devs
            ==> SubjPID(k, s_id) == SubjPID(k', s_id));

    assert AllTDIDs(k'.objects) == AllTDIDs(k.objects);
    assert AllFDIDs(k'.objects) == AllFDIDs(k.objects);
    assert AllDOIDs(k'.objects) == AllDOIDs(k.objects);

    assert MapGetKeys(BuildMap_ObjIDsToPIDs(k'.objects)) == MapGetKeys(BuildMap_ObjIDsToPIDs(k.objects));
    forall o_id | o_id in BuildMap_ObjIDsToPIDs(k.objects)
        ensures BuildMap_ObjIDsToPIDs(k'.objects)[o_id] == BuildMap_ObjIDsToPIDs(k.objects)[o_id]
    {
        // Dafny can automatically prove this lemma
    }
}

lemma Lemma_SameObjsOwnershipInSuccessiveStates(k:State, k':State)
    requires AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects)

    requires MapGetKeys(k.subjects.drvs) == MapGetKeys(k'.subjects.drvs)
    requires MapGetKeys(k.subjects.devs) == MapGetKeys(k'.subjects.devs)

    requires forall drv_id :: drv_id in k'.subjects.drvs
                ==> (k'.subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                    (k'.subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                    (k'.subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k'.subjects.devs
                ==> (k'.subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'.subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'.subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
    
    requires AllTDIDs(k'.objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'.objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'.objects) == AllDOIDs(k.objects)

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2

    ensures forall s_id, o_id :: 
                Drv_ID(s_id) in k.subjects.drvs || Dev_ID(s_id) in k.subjects.devs 
                ==> DoOwnObj(k, s_id, o_id) == DoOwnObj(k', s_id, o_id)
    ensures forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k'.subjects) && s_id2 in AllSubjsIDs(k'.subjects) && 
                DoOwnObj(k', s_id1, o_id) && DoOwnObj(k', s_id2, o_id)
                ==> s_id1 == s_id2
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SameObjsOwnershipInSuccessiveStates_SlimState(k:State, k'_subjects:Subjects, k'_objects:Objects)
    requires AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)

    requires MapGetKeys(k.subjects.drvs) == MapGetKeys(k'_subjects.drvs)
    requires MapGetKeys(k.subjects.devs) == MapGetKeys(k'_subjects.devs)

    requires forall drv_id :: drv_id in k'_subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                    (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                    (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
    
    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)

    requires forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2

    ensures forall s_id, o_id :: 
                Drv_ID(s_id) in k.subjects.drvs || Dev_ID(s_id) in k.subjects.devs 
                ==> DoOwnObj(k, s_id, o_id) == DoOwnObj_SlimState(k'_subjects, s_id, o_id)
    ensures forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k'_subjects) && s_id2 in AllSubjsIDs(k'_subjects) && 
                DoOwnObj_SlimState(k'_subjects, s_id1, o_id) && DoOwnObj_SlimState(k'_subjects, s_id2, o_id)
                ==> s_id1 == s_id2
{
    // Dafny can automatically prove this lemma
}

// Lemma: SubjPID_DevID of a device <dev_id> returns the same PID as
// SubjPID of the s_id of the <dev_id>
lemma Lemma_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID(k_subjects:Subjects, dev_id:Dev_ID)
    requires forall drv_sid, dev_sid :: 
                (Drv_ID(drv_sid) in k_subjects.drvs) && (Dev_ID(dev_sid) in k_subjects.devs)
                 ==> (drv_sid != dev_sid)
    //requires IsDevID(k, dev_id)
    requires dev_id in k_subjects.devs

    ensures SubjPID_DevID_SlimState(k_subjects, dev_id) == SubjPID_SlimState(k_subjects, dev_id.sid)
{
    assert Dev_ID(dev_id.sid) in k_subjects.devs;
    assert SubjPID_DevID_SlimState(k_subjects, dev_id) == k_subjects.devs[dev_id].pid;

    assert SubjPID_SlimState(k_subjects, dev_id.sid) == k_subjects.devs[Dev_ID(dev_id.sid)].pid;
}


// Lemma: For each device in the I/O system, SubjPID_DevID and SubjPID returns
// the same PID
lemma Lemma_AllDevsInStateReturnsSamePIDBySubjPIDDevIDAndSubjPID(k:State)
    requires forall drv_sid, dev_sid :: 
                (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
                    ==> (drv_sid != dev_sid)

    ensures forall dev_id {:trigger SubjPID_DevID(k, dev_id)} :: IsDevID(k, dev_id) 
                ==> SubjPID_DevID(k, dev_id) == SubjPID(k, dev_id.sid)
{
    forall dev_id | IsDevID(k, dev_id)
        ensures SubjPID_DevID(k, dev_id) == SubjPID(k, dev_id.sid)
    {
        Lemma_DevReturnsSamePIDBySubjPIDDevIDAndSubjPID(k.subjects, dev_id);
    }
}

lemma Lemma_ActiveDevsHaveHcodedPtrsToOwnedObjs(k:State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires forall s_id :: s_id in AllSubjsIDs(k.subjects)
                <==> (Drv_ID(s_id) in k.subjects.drvs) || (Dev_ID(s_id) in k.subjects.devs)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)

    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2)    
    requires forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> IDToDev(k, dev_id2).td_ids <= AllTDIDs(k.objects)

    ensures forall dev_id2 :: dev_id2 in AllActiveDevs(k)
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= AllTDIDs(k.objects)
{
    // Dafny can automatically prove this lemma.
}

lemma Lemma_OwnObjIDs_Property(k:State, s_id:Subject_ID)
    requires P_ObjsInSubjsAreAlsoInState(k)
    requires IsSubjID(k.subjects, s_id) 
    
    ensures forall o_id :: o_id in OwnObjIDs(k, s_id)
                ==> DoOwnObj(k, s_id, o_id)
{
    // Dafny can automatically prove this lemma
}

predicate K_UniqueIDsAndOwnedObjs(
    k_subjects:Subjects, k_objs_td_ids:set<TD_ID>, k_objs_fd_ids:set<FD_ID>, k_objs_do_ids:set<DO_ID>
)
{
    (forall drv_sid, dev_sid :: 
                 (Drv_ID(drv_sid) in k_subjects.drvs) && (Dev_ID(dev_sid) in k_subjects.devs)
                 ==> (drv_sid != dev_sid)) &&
        // Requirement: Subjects have different internal IDs
    (forall drv_id, td_id :: 
                drv_id in k_subjects.drvs && td_id in k_subjects.drvs[drv_id].td_ids
                ==> td_id in k_objs_td_ids) &&
    (forall drv_id, fd_id :: 
                drv_id in k_subjects.drvs && fd_id in k_subjects.drvs[drv_id].fd_ids
                ==> fd_id in k_objs_fd_ids) &&
    (forall drv_id, do_id :: 
                drv_id in k_subjects.drvs && do_id in k_subjects.drvs[drv_id].do_ids
                ==> do_id in k_objs_do_ids) &&
    (forall dev_id, td_id :: 
                dev_id in k_subjects.devs && td_id in k_subjects.devs[dev_id].td_ids
                ==> td_id in k_objs_td_ids) &&
    (forall dev_id, fd_id :: 
                dev_id in k_subjects.devs && fd_id in k_subjects.devs[dev_id].fd_ids
                ==> fd_id in k_objs_fd_ids) &&
    (forall dev_id, do_id :: 
                dev_id in k_subjects.devs && do_id in k_subjects.devs[dev_id].do_ids
                ==> do_id in k_objs_do_ids) &&
    ((forall td_id, fd_id :: TD_ID(td_id) in k_objs_td_ids && FD_ID(fd_id) in k_objs_fd_ids
                ==> td_id != fd_id) &&
            (forall td_id, do_id :: TD_ID(td_id) in k_objs_td_ids && DO_ID(do_id) in k_objs_do_ids
                ==> td_id != do_id) &&
            (forall fd_id, do_id :: FD_ID(fd_id) in k_objs_fd_ids && DO_ID(do_id) in k_objs_do_ids
                ==> fd_id != do_id)) &&
        // Requirement: Objects have different internal IDs
    (forall dev_id :: dev_id in k_subjects.devs
                ==> k_subjects.devs[dev_id].hcoded_td_id in k_subjects.devs[dev_id].td_ids) &&
        // Requirement: Devices own hardcoded TDs

    (true)
}

lemma Lemma_ActiveObjsMustInActiveSet_TD(k:State, td_id:TD_ID)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires td_id in AllTDIDs(k.objects)

    requires ObjPID(k, td_id.oid) != NULL
    requires td_id !in k.objects.hcoded_tds

    ensures td_id in k.objects.active_non_hcoded_tds
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ActiveObjsMustInActiveSet_FD(k:State, fd_id:FD_ID)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires fd_id in AllFDIDs(k.objects)

    requires ObjPID(k, fd_id.oid) != NULL

    ensures fd_id in k.objects.active_fds
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ActiveObjsMustInActiveSet_DO(k:State, do_id:DO_ID)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires do_id in AllDOIDs(k.objects)

    requires ObjPID(k, do_id.oid) != NULL

    ensures do_id in k.objects.active_dos
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_InActiveObjsMustInInActiveSet_TD(k:State, td_id:TD_ID)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k.objects)
    requires td_id in AllTDIDs(k.objects)

    requires ObjPID(k, td_id.oid) == NULL
    requires td_id !in k.objects.hcoded_tds

    ensures td_id in k.objects.inactive_non_hcoded_tds
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
}

lemma Lemma_InActiveObjsMustInInActiveSet_FD(k:State, fd_id:FD_ID)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k.objects)
    requires fd_id in AllFDIDs(k.objects)

    requires ObjPID(k, fd_id.oid) == NULL

    ensures fd_id in k.objects.inactive_fds
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
}

lemma Lemma_InActiveObjsMustInInActiveSet_DO(k:State, do_id:DO_ID)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k.objects)
    requires do_id in AllDOIDs(k.objects)

    requires ObjPID(k, do_id.oid) == NULL

    ensures do_id in k.objects.inactive_dos
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
}