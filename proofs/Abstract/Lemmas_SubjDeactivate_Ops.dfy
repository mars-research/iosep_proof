include "Syntax.dfy"
include "Properties.dfy"
include "Utils.dfy"
include "CASOps.dfy"
include "Lemmas.dfy"
include "Lemmas_Ops.dfy"
include "Lemmas_SubjDeactivate_ReachableTDsStates.dfy"
include "./BuildCAS/BuildCAS.dfy"

predicate SubjObjDeactivate_PropertiesOfTDs(k:State, k'_subjects:Subjects, k'_objects:Objects, todeactivate_td_ids:set<TD_ID>)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    requires forall dev_id :: dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> dev_id in AllActiveDevs(k)
{
    (MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)) &&
    (MapGetKeys(k.objects.hcoded_tds) == AllHCodedTDIDs(k.subjects)) &&

    (AllTDIDs(k'_objects) == AllTDIDs(k.objects)) &&
    (todeactivate_td_ids <= AllTDIDs(k.objects)) &&
    (forall td_id :: td_id in todeactivate_td_ids
            ==> ObjPID_KObjects(k'_objects, td_id.oid) == NULL) &&
    (forall td_id :: td_id in todeactivate_td_ids
            ==> ObjPID_KObjects(k.objects, td_id.oid) != NULL) &&

    (forall td_id :: td_id in k.objects.hcoded_tds
                ==> k'_objects.hcoded_tds[td_id].val == k.objects.hcoded_tds[td_id].val
    ) &&
        // Requirement: Immutable values in <hcoded_tds> are unchanged
    (forall td_id :: td_id in AllTDIDs(k.objects) &&
                    td_id !in todeactivate_td_ids
                ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id)
    ) &&
        // Requirement: TDs not to be deactivated are unchanged

    (forall tds_state2, td_id, dev_id :: tds_state2 in AllReachableActiveTDsStates(k) &&
                td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
            ==> DevAModesToObj(k, tds_state2, dev_id, td_id.oid) == {}) &&

    (true) 
}

predicate SubjObjDeactivate_PropertiesOfFDs(k:State, k'_subjects:Subjects, k'_objects:Objects, todeactivate_fd_ids:set<FD_ID>)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    requires forall dev_id :: dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> dev_id in AllActiveDevs(k)
{
    (AllFDIDs(k'_objects) == AllFDIDs(k.objects)) &&
    (todeactivate_fd_ids <= AllFDIDs(k.objects)) &&
    (forall fd_id :: fd_id in todeactivate_fd_ids
            ==> fd_id in k'_objects.inactive_fds
    ) &&
    (forall fd_id :: fd_id in todeactivate_fd_ids
            ==> fd_id in k.objects.active_fds &&
                k.objects.active_fds[fd_id].pid != NULL
    ) &&
    (forall fd_id :: fd_id in AllFDIDs(k.objects) &&
                fd_id !in todeactivate_fd_ids
            ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id)
    ) &&
    (forall tds_state2, fd_id, dev_id :: tds_state2 in AllReachableActiveTDsStates(k) &&
                fd_id in todeactivate_fd_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
            ==> DevAModesToObj(k, tds_state2, dev_id, fd_id.oid) == {}) &&
        // Requirement: All active devices in k' must have no access to FDs 
        // being deactivated

    (true)
}

predicate SubjObjDeactivate_PropertiesOfDOs(k:State, k'_subjects:Subjects, k'_objects:Objects, todeactivate_do_ids:set<DO_ID>)
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    requires forall dev_id :: dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> dev_id in AllActiveDevs(k)
{
    (AllDOIDs(k'_objects) == AllDOIDs(k.objects)) &&
    (todeactivate_do_ids <= AllDOIDs(k.objects)) &&
    (forall do_id :: do_id in todeactivate_do_ids
            ==> do_id in k'_objects.inactive_dos
    ) &&
    (forall do_id :: do_id in todeactivate_do_ids
            ==> do_id in k.objects.active_dos &&
                k.objects.active_dos[do_id].pid != NULL
    ) &&
    (forall do_id :: do_id in AllDOIDs(k.objects) &&
                do_id !in todeactivate_do_ids
            ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id)
    ) &&
    (forall tds_state2, do_id, dev_id :: tds_state2 in AllReachableActiveTDsStates(k) &&
                do_id in todeactivate_do_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
            ==> DevAModesToObj(k, tds_state2, dev_id, do_id.oid) == {}) &&
        // Requirement: All active devices in k' must have no access to DOs 
        // being deactivated

    (true)
}

predicate SubjObjDeactivate_PropertiesOfSubjs(
    k:State, k'_subjects:Subjects, todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)
{
    (AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)) &&
    (MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)) &&
    (MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)) &&

    (todeactivate_s_ids <= AllSubjsIDs(k.subjects)) &&
    (forall s_id :: s_id in todeactivate_s_ids 
                ==> OwnedTDs(k, s_id) <= todeactivate_td_ids &&
                    OwnedFDs(k, s_id) <= todeactivate_fd_ids &&
                    OwnedDOs(k, s_id) <= todeactivate_do_ids) &&
        // If a subject is to be deactivated, then its objects are also to be deactivated
    (forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k'_subjects, s_id) == NULL) &&
    (forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) != NULL) &&

    (forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
            ==> (Drv_ID(s_id) in k.subjects.drvs ==> k'_subjects.drvs[Drv_ID(s_id)] == k.subjects.drvs[Drv_ID(s_id)]) &&
                (Dev_ID(s_id) in k.subjects.devs ==> k'_subjects.devs[Dev_ID(s_id)] == k.subjects.devs[Dev_ID(s_id)])) &&
    (forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
            ==> OwnedTDs(k, s_id) * todeactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * todeactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * todeactivate_do_ids == {}) &&
        // If a subject is not to be deactivated, then its objects must not to be
        // deactivated

    (true)
}

lemma Lemma_SubjObjDeactivate_NewK_UniqueIDsAndOwnedObjs(k:State, k':State)
    requires IsValidState(k)
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')

    ensures K_UniqueIDsAndOwnedObjs(k'.subjects, AllTDIDs(k'.objects), AllFDIDs(k'.objects), AllDOIDs(k'.objects))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjDeactivate_FulfillCommonPreConditionsOfKAndNewK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures SubjObjDeactivate_PreConditionsOfK(k')
    ensures IsValidState_SubjsOwnObjsThenInSamePartition(k')
    ensures SubjObjDeactivate_CommonPreConditionsOfKAndNewK(k, k_params, k', k'_params,
                todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
{
    Lemma_SubjObjDeactivate_NewK_UniqueIDsAndOwnedObjs(k ,k');
    Lemma_SubjObjDeactivate_NewK_SubjsObjsPIDsInNewK(k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_SubjObjDeactivate_NewK_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_SubjObjDeactivate_NewK_FulfillNextThreePredicates(k, k_params, k', k'_params, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_SubjObjDeactivate_NewK_ReachableActiveTDsStatesInK_FulfillConditionsToObjsBeingDeactivated(k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_SubjObjDeactivate_NewK_ActiveObjsInNewKHasUnchangedPIDs(k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
}

lemma Lemma_SubjObjDeactivate_ActiveDevsInNewKHaveNoTransfersToObjsToBeDeactivated(
    k:State, k'_subjects:Subjects, k_cas:CAS, k_reachable_active_tds_states:set<TDs_Vals>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k)

    requires AllActiveDevs_SlimState(k'_subjects) <= AllActiveDevs(k)

    requires forall o_id, dev_id :: o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids) &&
                    dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}

    requires forall tds_state2 :: tds_state2 in k_reachable_active_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k)

    requires CASGetSubjs(k_cas) == AllActiveDevs(k)
    requires CASGetObjs(k_cas) == AllActiveObjs(k)
    requires forall dev_id2 :: IsSubjInCAS(k_cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(k_cas.m[dev_id2]) == k_cas.o_ids
        //// Requirement: The result CAS is a matrix
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> IsInCAS(k_cas, dev_id2, o_id2)
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in k_reachable_active_tds_states &&
                                R in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (W in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in k_reachable_active_tds_states &&
                                W in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
        // Requirement: k_cas = BuildCAS(k, KToKParams(k), k.reachable_active_tds_states)

    ensures forall tds_state2, td_id, dev_id :: tds_state2 in k_reachable_active_tds_states &&
                td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
            ==> DevAModesToObj(k, tds_state2, dev_id, td_id.oid) == {}
    ensures forall tds_state2, fd_id, dev_id :: tds_state2 in k_reachable_active_tds_states &&
                fd_id in todeactivate_fd_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
            ==> DevAModesToObj(k, tds_state2, dev_id, fd_id.oid) == {}
    ensures forall tds_state2, do_id, dev_id :: tds_state2 in k_reachable_active_tds_states &&
                do_id in todeactivate_do_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
            ==> DevAModesToObj(k, tds_state2, dev_id, do_id.oid) == {}
{
    forall tds_state2, td_id, dev_id | tds_state2 in k_reachable_active_tds_states &&
                td_id in todeactivate_td_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
        ensures DevAModesToObj(k, tds_state2, dev_id, td_id.oid) == {}
    {
        var o_id := td_id.oid;
        var amodes := DevAModesToObj(k, tds_state2, dev_id, td_id.oid);
        assert IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {};
        assert R !in amodes;
        assert W !in amodes;
        Lemma_EmptyAModesIsNoRAndNoW(amodes);
    }

    forall tds_state2, fd_id, dev_id | tds_state2 in k_reachable_active_tds_states &&
                fd_id in todeactivate_fd_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
        ensures DevAModesToObj(k, tds_state2, dev_id, fd_id.oid) == {}
    {
        var o_id := fd_id.oid;
        var amodes := DevAModesToObj(k, tds_state2, dev_id, fd_id.oid);
        assert IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {};
        assert R !in amodes;
        assert W !in amodes;
        Lemma_EmptyAModesIsNoRAndNoW(amodes);
    }

    forall tds_state2, do_id, dev_id | tds_state2 in k_reachable_active_tds_states &&
                do_id in todeactivate_do_ids &&
                dev_id in AllActiveDevs_SlimState(k'_subjects)
        ensures DevAModesToObj(k, tds_state2, dev_id, do_id.oid) == {}
    {
        var o_id := do_id.oid;
        var amodes := DevAModesToObj(k, tds_state2, dev_id, do_id.oid);
        assert IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {};
        assert R !in amodes;
        assert W !in amodes;
        Lemma_EmptyAModesIsNoRAndNoW(amodes);
    }
}

lemma Lemma_ExternalObjsDeactivate_AllObjsToBeDeactivatedAreExternalObjs(
    k:State,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    (TD_ID(o_id) in todeactivate_td_ids || FD_ID(o_id) in todeactivate_fd_ids || DO_ID(o_id) in todeactivate_do_ids)
                ==> !DoOwnObj(k, s_id, o_id)
        // Requirement: no subject owns these external objects

    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects)
            ==> OwnedTDs(k, s_id) * todeactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * todeactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * todeactivate_do_ids == {}

    ensures {} <= AllSubjsIDs(k.subjects)
{
    forall s_id | s_id in AllSubjsIDs(k.subjects)
        ensures OwnedTDs(k, s_id) * todeactivate_td_ids == {}
        ensures OwnedFDs(k, s_id) * todeactivate_fd_ids == {}
        ensures OwnedDOs(k, s_id) * todeactivate_do_ids == {}
    {
        assert forall td_id :: td_id in todeactivate_td_ids
                ==> !DoOwnObj(k, s_id, td_id.oid);
        assert forall fd_id :: fd_id in todeactivate_fd_ids
                ==> !DoOwnObj(k, s_id, fd_id.oid);
        assert forall do_id :: do_id in todeactivate_do_ids
                ==> !DoOwnObj(k, s_id, do_id.oid);

        assert forall td_id :: td_id in todeactivate_td_ids
                ==> td_id !in OwnedTDs(k, s_id);
        assert forall fd_id :: fd_id in todeactivate_fd_ids
                ==> fd_id !in OwnedFDs(k, s_id);
        assert forall do_id :: do_id in todeactivate_do_ids
                ==> do_id !in OwnedDOs(k, s_id);
    }

    Lemma_EmptySetIsSubsetOfAnySet(AllSubjsIDs(k.subjects));
}

// [NOTE] Needs 80s to verify
lemma Lemma_ExternalObjsDeactivate_ProveSubjsObjsFulfillProperties_PreConditions(
    k:State, k'_subjects:Subjects, k'_objects:Objects, 
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)
    requires IsValidState_SubjsOwnObjsThenInSamePartition(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs

    requires k'_subjects == k.subjects

    requires td_ids <= AllTDIDs(k.objects)
    requires fd_ids <= AllFDIDs(k.objects)
    requires do_ids <= AllDOIDs(k.objects)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)
    requires (forall td_id :: td_id in td_ids ==> ObjPID(k, td_id.oid) != NULL) &&
            (forall fd_id :: fd_id in fd_ids ==> ObjPID(k, fd_id.oid) != NULL) &&
            (forall do_id :: do_id in do_ids ==> ObjPID(k, do_id.oid) != NULL)

    requires (forall id :: id in td_ids ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in fd_ids ==> id in k.objects.active_fds) &&
            (forall id :: id in do_ids ==> id in k.objects.active_dos)

    requires var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, td_ids);
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fd_ids);
            k'_objects == SetPIDs_ActiveDOs_ToNULLPID(t_objs2, do_ids)

    ensures forall td_id :: td_id in td_ids
                ==> ObjPID_KObjects(k.objects, td_id.oid) != NULL && ObjPID_KObjects(k'_objects, td_id.oid) == NULL
    ensures forall td_id :: td_id in k.objects.hcoded_tds
                ==> k'_objects.hcoded_tds[td_id].val == k.objects.hcoded_tds[td_id].val
    ensures forall td_id :: td_id in AllTDIDs(k.objects) &&
                td_id !in td_ids
            ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id)
    ensures forall fd_id :: fd_id in fd_ids
                ==> ObjPID_KObjects(k.objects, fd_id.oid) != NULL && ObjPID_KObjects(k'_objects, fd_id.oid) == NULL
    ensures forall fd_id :: fd_id in AllFDIDs(k.objects) &&
                fd_id !in fd_ids
            ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id)
    ensures forall do_id :: do_id in do_ids
                ==> ObjPID_KObjects(k.objects, do_id.oid) != NULL && ObjPID_KObjects(k'_objects, do_id.oid) == NULL
    ensures forall do_id :: do_id in AllDOIDs(k.objects) &&
                do_id !in do_ids
            ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id)
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    forall fd_id | fd_id in fd_ids
        ensures ObjPID_KObjects(k.objects, fd_id.oid) != NULL
        ensures ObjPID_KObjects(k'_objects, fd_id.oid) == NULL
    {
       // Dafny can automatically prove it
    }
}

// [NOTE] Needs 150s to verify
lemma Lemma_ExternalObjsDeactivate_ProveSubjsObjsFulfillProperties(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k_cas:CAS,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_tds) <= 
                        IDToDev(k, dev_id).td_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_fds) <= 
                        IDToDev(k, dev_id).fd_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_dos) <= 
                        IDToDev(k, dev_id).do_ids)

    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)
    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires MapGetKeys(k.objects.hcoded_tds) == AllHCodedTDIDs(k.subjects)

    requires k'_subjects == k.subjects

    requires td_ids <= AllTDIDs(k.objects)
    requires fd_ids <= AllFDIDs(k.objects)
    requires do_ids <= AllDOIDs(k.objects)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)

    requires forall o_id, dev_id :: o_id in TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids) &&
                    dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}
    requires CASGetSubjs(k_cas) == AllActiveDevs(k)
    requires CASGetObjs(k_cas) == AllActiveObjs(k)
    requires forall dev_id2 :: IsSubjInCAS(k_cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(k_cas.m[dev_id2]) == k_cas.o_ids
        //// Requirement: The result CAS is a matrix
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> IsInCAS(k_cas, dev_id2, o_id2)
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k) &&
                                R in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (W in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k) &&
                                W in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
        // Requirement: k_cas = BuildCAS(k, KToKParams(k), AllReachableActiveTDsStates(k))

    requires forall td_id :: td_id in td_ids
                ==> ObjPID_KObjects(k.objects, td_id.oid) != NULL && ObjPID_KObjects(k'_objects, td_id.oid) == NULL
    requires forall td_id :: td_id in k.objects.hcoded_tds
                ==> k'_objects.hcoded_tds[td_id].val == k.objects.hcoded_tds[td_id].val
    requires forall td_id :: td_id in AllTDIDs(k.objects) &&
                td_id !in td_ids
            ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id)
    requires forall fd_id :: fd_id in fd_ids
                ==> ObjPID_KObjects(k.objects, fd_id.oid) != NULL && ObjPID_KObjects(k'_objects, fd_id.oid) == NULL
    requires forall fd_id :: fd_id in AllFDIDs(k.objects) &&
                fd_id !in fd_ids
            ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id)
    requires forall do_id :: do_id in do_ids
                ==> ObjPID_KObjects(k.objects, do_id.oid) != NULL && ObjPID_KObjects(k'_objects, do_id.oid) == NULL
    requires forall do_id :: do_id in AllDOIDs(k.objects) &&
                do_id !in do_ids
            ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id)

    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k'_objects)

    ensures SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, td_ids)
    ensures SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, fd_ids)
    ensures SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, do_ids)
    ensures SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, {}, 
                td_ids, fd_ids, do_ids)
{
    var tds_owned_by_drv:set<TD_ID> := td_ids;
    var fds_owned_by_drv:set<FD_ID> := fd_ids;
    var dos_owned_by_drv:set<DO_ID> := do_ids;

    var todeactivate_s_ids:set<Subject_ID> := {};
    var todeactivate_td_ids := tds_owned_by_drv;
    var todeactivate_fd_ids := fds_owned_by_drv;
    var todeactivate_do_ids := dos_owned_by_drv;

    Lemma_SubjObjDeactivate_ActiveDevsInNewKHaveNoTransfersToObjsToBeDeactivated(
            k, k'_subjects, k_cas, AllReachableActiveTDsStates(k), 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    assert SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids);

    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    forall fd_id | fd_id in todeactivate_fd_ids
        ensures fd_id in k'_objects.inactive_fds
    {
        assert fd_id in AllFDIDs(k'_objects);
        assert ObjPID_KObjects(k'_objects, fd_id.oid) == NULL;
        reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    }

    assert SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids);
    assert SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids);

    Lemma_ExternalObjsDeactivate_AllObjsToBeDeactivatedAreExternalObjs(k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    assert SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
}

lemma Lemma_SubjObjDeactivate_NewKParams_HasUnmodifiedVarsFromKParams(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
        // Requirement: Hardcoded TDs are in devices
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)

    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)
    requires forall drv_id :: drv_id in k'_subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)

    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)
        // Requriement: TD/FD/DO IDs are not changed
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires MapGetKeys(k.objects.hcoded_tds) == AllHCodedTDIDs(k.subjects)

    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_objects.hcoded_tds[k'_subjects.devs[dev_id].hcoded_td_id].val == k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val
        // Requirement: Hardcoded TDs are immutable

    requires k'_params == ReachableTDsKParams(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects))

    ensures MapGetKeys(k'_params.subjects.drvs) == MapGetKeys(KToKParams(k).subjects.drvs)
    ensures MapGetKeys(k'_params.subjects.devs) == MapGetKeys(KToKParams(k).subjects.devs)
    ensures k'_params.objs_td_ids == KToKParams(k).objs_td_ids
    ensures k'_params.objs_fd_ids == KToKParams(k).objs_fd_ids
    ensures k'_params.objs_do_ids == KToKParams(k).objs_do_ids
    ensures k'_params.hcoded_td_ids == KToKParams(k).hcoded_td_ids
    ensures k'_params.hcoded_tds == KToKParams(k).hcoded_tds
    ensures MapGetKeys(k'_params.objs_pids) == MapGetKeys(KToKParams(k).objs_pids)
{
    assert AllTDIDs(k'_objects) == AllTDIDs(k.objects);
    assert AllFDIDs(k'_objects) == AllFDIDs(k.objects);
    assert AllDOIDs(k'_objects) == AllDOIDs(k.objects);

    assert forall dev_id :: dev_id in k.subjects.devs
                ==> k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids;
    assert forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                    (k'_objects.hcoded_tds[k'_subjects.devs[dev_id].hcoded_td_id].val == k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val);

    Lemma_NewStateVars_HCodedTDsAreUnmodified(k, k'_subjects, k'_objects);
}

lemma Lemma_ExternalObjsDeactivate_SubjsAndTheirObjsHaveSamePIDs(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams,
    tds_to_deactivate:set<TD_ID>, fds_to_deactivate:set<FD_ID>, dos_to_deactivate:set<DO_ID>
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires K_UniqueIDsAndOwnedObjs(k.subjects, AllTDIDs(k.objects), AllFDIDs(k.objects), AllDOIDs(k.objects))

    requires k'_subjects == k.subjects
    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)
    requires AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)
    requires AllObjsIDs(k'_objects) == AllObjsIDs(k.objects)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in AllTDIDs(k.objects)
        // Requirement: Hardcoded TDs are in the TDs of the state
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds
    requires tds_to_deactivate <= AllTDIDs(k.objects)
    requires fds_to_deactivate <= AllFDIDs(k.objects)
    requires dos_to_deactivate <= AllDOIDs(k.objects)
    requires forall s_id, td_id :: s_id in AllSubjsIDs(k.subjects) &&
                    td_id in tds_to_deactivate
                ==> !DoOwnObj(k, s_id, td_id.oid)
    requires forall s_id, fd_id :: s_id in AllSubjsIDs(k.subjects) &&
                    fd_id in fds_to_deactivate
                ==> !DoOwnObj(k, s_id, fd_id.oid)
    requires forall s_id, do_id :: s_id in AllSubjsIDs(k.subjects) &&
                    do_id in dos_to_deactivate
                ==> !DoOwnObj(k, s_id, do_id.oid)
        // Requirement: TDs/FDs/DOs to be activated must be external TDs/FDs/DOs
    requires forall td_id :: td_id in AllTDIDs(k.objects) && td_id !in tds_to_deactivate
                ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id)
    requires forall fd_id :: fd_id in AllFDIDs(k.objects) && fd_id !in fds_to_deactivate
                ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id)
    requires forall do_id :: do_id in AllDOIDs(k.objects) && do_id !in dos_to_deactivate
                ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id)
        // Requirement: Other TDs/FDs/DOs are not modified

    requires forall s_id, o_id :: s_id in AllSubjsIDs(KToKParams(k).subjects) &&
                    DoOwnObj_SlimState(KToKParams(k).subjects, s_id, o_id)
                ==> o_id in KToKParams(k).objs_pids &&
                    KToKParams(k).objs_pids[o_id] == SubjPID_SlimState(KToKParams(k).subjects, s_id)
        // Requirement: In k, if a subject owns an object, then the subject 
        // and the object must be in the same partition
    
    requires forall dev_id, td_id :: 
                dev_id in k'_subjects.devs && td_id in k'_subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k'_objects) 
    requires k'_params == ReachableTDsKParams(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects))

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
                ==> o_id in k'_params.objs_pids &&
                    k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
{
    assert AllTDIDs(k'_objects) == AllTDIDs(k.objects);
    assert AllFDIDs(k'_objects) == AllFDIDs(k.objects);
    assert AllDOIDs(k'_objects) == AllDOIDs(k.objects);

    assert k'_params.subjects == KToKParams(k).subjects;

    forall dev_id, hcoded_td_id | dev_id in k.subjects.devs &&
                hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id
        ensures DoOwnObj_SlimState(k.subjects, dev_id.sid, hcoded_td_id.oid)
    {
        Lemma_DevsOwnHCodedTDs(k.subjects, dev_id, hcoded_td_id);
    }

    forall s_id, o_id | s_id in AllSubjsIDs(k'_params.subjects) &&
                        DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
        ensures o_id in k'_params.objs_pids &&
                k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
    {
        assert IsSubjID(k.subjects, s_id);
        assert o_id in AllObjsIDs(k'_objects);
        assert MapGetKeys(BuildMap_ObjIDsToPIDs(k'_objects)) == AllObjsIDs(k'_objects);
        assert k'_params.objs_pids == BuildMap_ObjIDsToPIDs(k'_objects);
        assert o_id in k'_params.objs_pids;

        assert SubjPID_SlimState(k'_params.subjects, s_id) == SubjPID(k, s_id);
        if(TD_ID(o_id) in AllTDIDs(k.objects))
        {
            var td_id := TD_ID(o_id);
            assert td_id !in tds_to_deactivate;
            assert ObjStateUnchanged_TD(k.objects, k'_objects, td_id);
            assert k'_params.objs_pids[o_id] == ObjPID_KObjects(k.objects, td_id.oid);
        }
        else if(FD_ID(o_id) in AllFDIDs(k.objects))
        {
            var fd_id := FD_ID(o_id);
            assert fd_id !in fds_to_deactivate;
            assert ObjStateUnchanged_FD(k.objects, k'_objects, fd_id);
            assert k'_params.objs_pids[o_id] == ObjPID_KObjects(k.objects, fd_id.oid);
        }
        else
        {
            var do_id := DO_ID(o_id);
            assert DO_ID(o_id) in AllDOIDs(k.objects);
            assert do_id !in dos_to_deactivate;
            assert ObjStateUnchanged_DO(k.objects, k'_objects, do_id);
            assert k'_params.objs_pids[o_id] == ObjPID_KObjects(k.objects, do_id.oid);
        }
    }
}

lemma Lemma_SubjObjDeactivate_FindReachableActiveTDsStatesFromActiveTDsState_ReturnsReachableTDsStates(
    k':State, k'_params:ReachableTDsKParams, k'_active_devs:set<Dev_ID>, k'_active_tds_state:TDs_Vals,
    explored_tds_states:seq<set<TDs_Vals>>, found_tds_states:set<TDs_Vals>
)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_PreConditionsOfK(k')
    
    requires k'_params == KToKParams(k')
    requires k'_active_devs == AllActiveDevs(k')
    requires k'_active_tds_state == ActiveTDsState_SlimState(k'.objects)
    requires found_tds_states == GetExploredTDsStates(explored_tds_states, 0)

    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> TDsStateGetTDIDs(tds_state2) == k'_params.all_active_tds
    requires forall tds_state2 :: tds_state2 in GetExploredTDsStates(explored_tds_states, 0)
                ==> (k'_active_tds_state == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k'_params, k'_active_devs, k'_active_tds_state, tds_state2))

    ensures forall tds_state2 :: tds_state2 in found_tds_states
                ==> TDsStateGetTDIDs(tds_state2) == AllActiveTDs(k')
    ensures forall tds_state2 :: tds_state2 in found_tds_states
                ==> (ActiveTDsState(k') == tds_state2 || IsActiveTDsStateReachActiveTDsStateInChain(k'_params, 
                                AllActiveDevs(k'), ActiveTDsState(k'), tds_state2))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjDeactivate_NewK_FulfillSI2(
    k:State, k':State,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k.pids == k'.pids

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures IsSecureState_SI2(k')
{
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);

    forall s_id | s_id in AllSubjsIDs(k'.subjects) && SubjPID(k', s_id) != NULL
        ensures SubjPID(k', s_id) in k'.pids
    {
        assert s_id in todeactivate_s_ids || SubjPID(k, s_id) != NULL;
        assert s_id in AllSubjsIDs(k.subjects);
    }

    forall o_id | o_id in AllObjsIDs(k'.objects) && ObjPID(k', o_id) != NULL
        ensures ObjPID(k', o_id) in k'.pids
    {
        // Dafny can automatically prove this lemma
    }
}

lemma Lemma_DrvDevDeactivate_SubjsNotBeingDeactivatedDoNotOwnAnyObjsBeingDeactivated(
    k:State, k'_subjects:Subjects, todeactivate_s_ids:set<Subject_ID>,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k)

    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)

    requires todeactivate_s_ids <= AllSubjsIDs(k.subjects)
    requires forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k'_subjects, s_id) == NULL
        // Requirement: All subjects to be activated are inactive in k' 
    requires forall td_id :: td_id in todeactivate_td_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in todeactivate_fd_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in todeactivate_do_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    ensures forall s_id :: s_id in todeactivate_s_ids
            ==> s_id !in AllActiveSubjs_SlimState(k'_subjects)
    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
            ==> OwnedTDs(k, s_id) * todeactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * todeactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * todeactivate_do_ids == {}
{
    assert forall s_id :: s_id in todeactivate_s_ids
            ==> s_id !in AllActiveSubjs_SlimState(k'_subjects);

    assert forall o_id, s_id1, s_id2 :: 
        s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
        DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
        ==> s_id1 == s_id2;

    forall s_id | s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
        ensures OwnedTDs(k, s_id) * todeactivate_td_ids == {}
        ensures OwnedFDs(k, s_id) * todeactivate_fd_ids == {}
        ensures OwnedDOs(k, s_id) * todeactivate_do_ids == {}
    { 
        if(exists td_id :: td_id in OwnedTDs(k, s_id) && td_id in todeactivate_td_ids)
        {
            var td_id :| td_id in OwnedTDs(k, s_id) && td_id in todeactivate_td_ids;
            var s_id2 :| s_id2 in todeactivate_s_ids && td_id in OwnedTDs(k, s_id2);

            // Show conflict
            assert DoOwnObj(k, s_id, td_id.oid);
            assert DoOwnObj(k, s_id2, td_id.oid);
        }

        if(exists fd_id :: fd_id in OwnedFDs(k, s_id) && fd_id in todeactivate_fd_ids)
        {
            var fd_id :| fd_id in OwnedFDs(k, s_id) && fd_id in todeactivate_fd_ids;
            var s_id2 :| s_id2 in todeactivate_s_ids && fd_id in OwnedFDs(k, s_id2);

            // Show conflict
            assert DoOwnObj(k, s_id, fd_id.oid);
            assert DoOwnObj(k, s_id2, fd_id.oid);
        }

        if(exists do_id :: do_id in OwnedDOs(k, s_id) && do_id in todeactivate_do_ids)
        {
            var do_id :| do_id in OwnedDOs(k, s_id) && do_id in todeactivate_do_ids;
            var s_id2 :| s_id2 in todeactivate_s_ids && do_id in OwnedDOs(k, s_id2);

            // Show conflict
            assert DoOwnObj(k, s_id, do_id.oid);
            assert DoOwnObj(k, s_id2, do_id.oid);
        }
    }
}

lemma Lemma_DrvDeactivate_ProveSubjsObjsFulfillProperties(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k_cas:CAS,
    todeactivate_drv_id:Drv_ID, new_drv_state:Drv_State
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_tds) <= 
                        IDToDev(k, dev_id).td_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_fds) <= 
                        IDToDev(k, dev_id).fd_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_dos) <= 
                        IDToDev(k, dev_id).do_ids)

    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)
    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires MapGetKeys(k.objects.hcoded_tds) == AllHCodedTDIDs(k.subjects)

    requires todeactivate_drv_id in k.subjects.drvs
    requires k'_subjects == Subjects(k.subjects.drvs[todeactivate_drv_id := new_drv_state], k.subjects.devs)

    requires new_drv_state.pid == NULL

    requires forall o_id, dev_id :: o_id in TDIDsToObjIDs(k.subjects.drvs[todeactivate_drv_id].td_ids) + 
                                            FDIDsToObjIDs(k.subjects.drvs[todeactivate_drv_id].fd_ids) + 
                                            DOIDsToObjIDs(k.subjects.drvs[todeactivate_drv_id].do_ids) &&
                    dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}
    requires CASGetSubjs(k_cas) == AllActiveDevs(k)
    requires CASGetObjs(k_cas) == AllActiveObjs(k)
    requires forall dev_id2 :: IsSubjInCAS(k_cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(k_cas.m[dev_id2]) == k_cas.o_ids
        //// Requirement: The result CAS is a matrix
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> IsInCAS(k_cas, dev_id2, o_id2)
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k) &&
                                R in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (W in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k) &&
                                W in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
        // Requirement: k_cas = BuildCAS(k, KToKParams(k), AllReachableActiveTDsStates(k))

    requires forall td_id :: td_id in k.subjects.drvs[todeactivate_drv_id].td_ids
                ==> td_id.oid in AllObjsIDs(k.objects)
    requires forall fd_id :: fd_id in k.subjects.drvs[todeactivate_drv_id].fd_ids
                ==> fd_id.oid in AllObjsIDs(k.objects)
    requires forall do_id :: do_id in k.subjects.drvs[todeactivate_drv_id].do_ids
                ==> do_id.oid in AllObjsIDs(k.objects)
        // Requirement: Properties can be proved with other properties, but Dafny cannot easily find it

    requires forall fd_id :: fd_id in k.subjects.drvs[todeactivate_drv_id].fd_ids
                ==> fd_id in k'_objects.inactive_fds
    requires forall do_id :: do_id in k.subjects.drvs[todeactivate_drv_id].do_ids
                ==> do_id in k'_objects.inactive_dos
        // Requirement: FDs and DOs to be deactivated are put into <inactive_fds/dos>

    requires SubjPID_SlimState(k.subjects, todeactivate_drv_id.sid) != NULL
        // Requirement: the driver to be deactivated must be active in k
    requires forall td_id :: td_id in k.subjects.drvs[todeactivate_drv_id].td_ids
                ==> ObjPID_KObjects(k.objects, td_id.oid) != NULL && ObjPID_KObjects(k'_objects, td_id.oid) == NULL
    requires forall td_id :: td_id in k.objects.hcoded_tds
                ==> k'_objects.hcoded_tds[td_id].val == k.objects.hcoded_tds[td_id].val
    requires forall td_id :: td_id in AllTDIDs(k.objects) &&
                td_id !in k.subjects.drvs[todeactivate_drv_id].td_ids
            ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id)
    requires forall fd_id :: fd_id in k.subjects.drvs[todeactivate_drv_id].fd_ids
                ==> ObjPID_KObjects(k.objects, fd_id.oid) != NULL && ObjPID_KObjects(k'_objects, fd_id.oid) == NULL
    requires forall fd_id :: fd_id in AllFDIDs(k.objects) &&
                fd_id !in k.subjects.drvs[todeactivate_drv_id].fd_ids
            ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id)
    requires forall do_id :: do_id in k.subjects.drvs[todeactivate_drv_id].do_ids
                ==> ObjPID_KObjects(k.objects, do_id.oid) != NULL && ObjPID_KObjects(k'_objects, do_id.oid) == NULL
    requires forall do_id :: do_id in AllDOIDs(k.objects) &&
                do_id !in k.subjects.drvs[todeactivate_drv_id].do_ids
            ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id)

    ensures SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, k.subjects.drvs[todeactivate_drv_id].td_ids)
    ensures SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, k.subjects.drvs[todeactivate_drv_id].fd_ids)
    ensures SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, k.subjects.drvs[todeactivate_drv_id].do_ids)
    ensures SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, {todeactivate_drv_id.sid}, 
                k.subjects.drvs[todeactivate_drv_id].td_ids, k.subjects.drvs[todeactivate_drv_id].fd_ids, k.subjects.drvs[todeactivate_drv_id].do_ids)
{
    var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[todeactivate_drv_id].td_ids;
    var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[todeactivate_drv_id].fd_ids;
    var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[todeactivate_drv_id].do_ids;

    var todeactivate_s_ids:set<Subject_ID> := {todeactivate_drv_id.sid};
    var todeactivate_td_ids := tds_owned_by_drv;
    var todeactivate_fd_ids := fds_owned_by_drv;
    var todeactivate_do_ids := dos_owned_by_drv;

    Lemma_SubjObjDeactivate_ActiveDevsInNewKHaveNoTransfersToObjsToBeDeactivated(
            k, k'_subjects, k_cas, AllReachableActiveTDsStates(k), 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_DrvDevDeactivate_SubjsNotBeingDeactivatedDoNotOwnAnyObjsBeingDeactivated(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_DrvDevDeactivate_AllObjsToBeActivatedAreActiveInK(k, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    assert SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids);
    assert SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids);
    assert SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids);
    assert SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
}

lemma Lemma_DrvDeactivate_ActiveDevsInNewKAreSubsetOfOnesInK_PreConditions(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_drv_id:Drv_ID, new_drv_state:Drv_State
)
    requires todeactivate_drv_id in k.subjects.drvs
    requires k'_subjects == Subjects(k.subjects.drvs[todeactivate_drv_id := new_drv_state], k.subjects.devs)

    requires SubjPID(k, todeactivate_drv_id.sid) != NULL
    requires new_drv_state.pid == NULL
    requires todeactivate_s_ids == {todeactivate_drv_id.sid}

    ensures todeactivate_s_ids <= AllSubjsIDs(k.subjects)
    ensures MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)

    ensures forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k'_subjects, s_id) == NULL
    ensures forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) != NULL
    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
            ==> (Drv_ID(s_id) in k.subjects.drvs ==> k'_subjects.drvs[Drv_ID(s_id)] == k.subjects.drvs[Drv_ID(s_id)]) &&
                (Dev_ID(s_id) in k.subjects.devs ==> k'_subjects.devs[Dev_ID(s_id)] == k.subjects.devs[Dev_ID(s_id)])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDeactivate_ProveSubjsObjsFulfillProperties_PreConditions(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k_cas:CAS,
    todeactivate_drv_id:Drv_ID, new_drv_state:Drv_State
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs

    requires todeactivate_drv_id in k.subjects.drvs
    requires k'_subjects == Subjects(k.subjects.drvs[todeactivate_drv_id := new_drv_state], k.subjects.devs)

    requires SubjPID(k, todeactivate_drv_id.sid) != NULL
    requires new_drv_state.pid == NULL

    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)

    requires forall td_id :: td_id in AllTDIDs(k.objects)
                ==> (td_id in k.subjects.drvs[todeactivate_drv_id].td_ids ==> ObjPID_KObjects(k'_objects, td_id.oid) == NULL) &&
                    (td_id !in k.subjects.drvs[todeactivate_drv_id].td_ids ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id))
    requires forall fd_id :: fd_id in AllFDIDs(k.objects)
                ==> (fd_id in k.subjects.drvs[todeactivate_drv_id].fd_ids ==> ObjPID_KObjects(k'_objects, fd_id.oid) == NULL) &&
                    (fd_id !in k.subjects.drvs[todeactivate_drv_id].fd_ids ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id))
    requires forall do_id :: do_id in AllDOIDs(k.objects)
                ==> (do_id in k.subjects.drvs[todeactivate_drv_id].do_ids ==> ObjPID_KObjects(k'_objects, do_id.oid) == NULL) &&
                    (do_id !in k.subjects.drvs[todeactivate_drv_id].do_ids ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id))

    requires P_ObjsInSubjsAreAlsoInState(k)
    requires forall o_id, dev_id :: o_id in OwnObjIDs(k, todeactivate_drv_id.sid) && dev_id in AllActiveDevs(k) 
            ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}

    requires forall td_id :: td_id in k.objects.hcoded_tds
                ==> k'_objects.hcoded_tds[td_id].val == k.objects.hcoded_tds[td_id].val
        // Requirement: <val> of hardcoded TDs are unchanged   

    ensures forall o_id, dev_id :: o_id in TDIDsToObjIDs(k.subjects.drvs[todeactivate_drv_id].td_ids) + 
                                            FDIDsToObjIDs(k.subjects.drvs[todeactivate_drv_id].fd_ids) + 
                                            DOIDsToObjIDs(k.subjects.drvs[todeactivate_drv_id].do_ids) &&
                    dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}
    ensures forall td_id :: td_id in k.subjects.drvs[todeactivate_drv_id].td_ids
                ==> ObjPID_KObjects(k.objects, td_id.oid) != NULL && ObjPID_KObjects(k'_objects, td_id.oid) == NULL
    ensures forall td_id :: td_id in AllTDIDs(k.objects) &&
                td_id !in k.subjects.drvs[todeactivate_drv_id].td_ids
            ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id)
    ensures forall fd_id :: fd_id in k.subjects.drvs[todeactivate_drv_id].fd_ids
                ==> ObjPID_KObjects(k.objects, fd_id.oid) != NULL && ObjPID_KObjects(k'_objects, fd_id.oid) == NULL
    ensures forall fd_id :: fd_id in AllFDIDs(k.objects) &&
                fd_id !in k.subjects.drvs[todeactivate_drv_id].fd_ids
            ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id)
    ensures forall do_id :: do_id in k.subjects.drvs[todeactivate_drv_id].do_ids
                ==> ObjPID_KObjects(k.objects, do_id.oid) != NULL && ObjPID_KObjects(k'_objects, do_id.oid) == NULL
    ensures forall do_id :: do_id in AllDOIDs(k.objects) &&
                do_id !in k.subjects.drvs[todeactivate_drv_id].do_ids
            ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id)
{
    forall td_id | td_id in k.subjects.drvs[todeactivate_drv_id].td_ids
        ensures ObjPID_KObjects(k.objects, td_id.oid) != NULL
    {
        assert DoOwnObj(k, todeactivate_drv_id.sid, td_id.oid);
    }
    forall fd_id | fd_id in k.subjects.drvs[todeactivate_drv_id].fd_ids
        ensures ObjPID_KObjects(k.objects, fd_id.oid) != NULL
    {
        assert DoOwnObj(k, todeactivate_drv_id.sid, fd_id.oid);
    }
    forall do_id | do_id in k.subjects.drvs[todeactivate_drv_id].do_ids
        ensures ObjPID_KObjects(k.objects, do_id.oid) != NULL
    {
        assert DoOwnObj(k, todeactivate_drv_id.sid, do_id.oid);
    }
}

lemma Lemma_DrvDevDeactivate_ActiveDevsInNewKAreSubsetOfOnesInK(
    k:State, k'_subjects:Subjects, todeactivate_s_ids:set<Subject_ID>
)
    requires todeactivate_s_ids <= AllSubjsIDs(k.subjects)

    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)

    requires forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k'_subjects, s_id) == NULL
    requires forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) != NULL
    requires forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
            ==> (Drv_ID(s_id) in k.subjects.drvs ==> k'_subjects.drvs[Drv_ID(s_id)] == k.subjects.drvs[Drv_ID(s_id)]) &&
                (Dev_ID(s_id) in k.subjects.devs ==> k'_subjects.devs[Dev_ID(s_id)] == k.subjects.devs[Dev_ID(s_id)])

    ensures AllActiveDevs_SlimState(k'_subjects) <= AllActiveDevs(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires todeactivate_s_ids <= AllSubjsIDs(k.subjects) 
    requires forall td_id :: td_id in todeactivate_td_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in todeactivate_fd_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in todeactivate_do_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids)

    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_subjects.devs[dev_id].hcoded_td_id in k'_subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k'_subjects.devs && td_id in k'_subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k'_objects)

    requires k'_params == ReachableTDsKParams(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects))

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
                ==> o_id in k'_params.objs_pids &&
                    k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
{
    Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs_OwnedObjsAreInNewK(k, k'_subjects, k'_objects, k'_params, 
        todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);

    forall s_id, o_id | s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
        ensures k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
    {
        if(s_id in todeactivate_s_ids)
        {
            Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsBeingDeactivated(
                k, k'_subjects, k'_objects, k'_params, 
                todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, s_id, o_id);
        }
        else
        {
            Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsNotBeingDeactivated(
                k, k'_subjects, k'_objects, k'_params, 
                todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, s_id, o_id);
        }
    }
}

lemma Lemma_DrvDeactivate_OwnershipOfObjsIsPreserved(
    k:State, k'_subjects:Subjects,
    todeactivate_drv_id:Drv_ID, new_drv_state:Drv_State
)
    requires todeactivate_drv_id in k.subjects.drvs
    requires k'_subjects == Subjects(k.subjects.drvs[todeactivate_drv_id := new_drv_state], k.subjects.devs)

    requires new_drv_state.td_ids == IDToDrv(k, todeactivate_drv_id).td_ids
    requires new_drv_state.fd_ids == IDToDrv(k, todeactivate_drv_id).fd_ids
    requires new_drv_state.do_ids == IDToDrv(k, todeactivate_drv_id).do_ids

    ensures forall drv_id :: drv_id in k'_subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDeactivate_SameSetOfActiveDevsInNewKAndK(
    k:State, k'_subjects:Subjects,
    todeactivate_drv_id:Drv_ID, new_drv_state:Drv_State
)
    requires IsValidState(k)
    requires todeactivate_drv_id in k.subjects.drvs
    requires k'_subjects == Subjects(k.subjects.drvs[todeactivate_drv_id := new_drv_state], k.subjects.devs)

    ensures AllActiveDevs_SlimState(k'_subjects) == AllActiveDevs(k)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_ActiveDevsInNewKAreSubsetOfOnesInK_PreConditions(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState(k)

    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires SubjPID(k, todeactivate_dev_id.sid) != NULL
    requires new_dev_state.pid == NULL
    requires todeactivate_s_ids == {todeactivate_dev_id.sid}

    ensures todeactivate_s_ids <= AllSubjsIDs(k.subjects)
    ensures MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    ensures MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)

    ensures forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k'_subjects, s_id) == NULL
    ensures forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) != NULL
    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in todeactivate_s_ids
            ==> (Drv_ID(s_id) in k.subjects.drvs ==> k'_subjects.drvs[Drv_ID(s_id)] == k.subjects.drvs[Drv_ID(s_id)]) &&
                (Dev_ID(s_id) in k.subjects.devs ==> k'_subjects.devs[Dev_ID(s_id)] == k.subjects.devs[Dev_ID(s_id)])
{
    // Dafny can automatically prove this lemma
    forall s_id | s_id in todeactivate_s_ids
        ensures SubjPID_SlimState(k'_subjects, s_id) == NULL
    {
        assert s_id == todeactivate_dev_id.sid;
        assert Dev_ID(s_id) in k.subjects.devs;
        assert Dev_ID(s_id) in k'_subjects.devs;
        assert Drv_ID(s_id) !in k'_subjects.drvs;

        assert SubjPID_SlimState(k'_subjects, s_id) == k'_subjects.devs[Dev_ID(s_id)].pid;
    }
}

lemma Lemma_DevDeactivate_ProveHCodedTDsAreRecordedInObjs_InNewK(
    k:State, dev_id:Dev_ID, k'_subjects:Subjects, k'_objects:Objects
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires dev_id in k.subjects.devs
    requires (forall id :: id in k.subjects.devs[dev_id].td_ids && id != k.subjects.devs[dev_id].hcoded_td_id ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.active_fds) &&
            (forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.active_dos)

    requires var dev_state := IDToDev(k, dev_id);
            var new_dev_state := Dev_State(NULL, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
            var new_devs := k.subjects.devs[dev_id := new_dev_state];
            k'_subjects == Subjects(k.subjects.drvs, new_devs)

    ensures var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
            var todeactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
            var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
            var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);
            todeactive_hcoded_td_id in t_objs3.hcoded_tds &&

            var k'_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);
            forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_subjects.devs[dev_id].hcoded_td_id in k'_objects.hcoded_tds
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    var todeactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
    var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
    var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);

    // Prove toactive_hcoded_td_id in t_objs3.hcoded_tds
    assert todeactive_hcoded_td_id in k.objects.hcoded_tds;
    assert todeactive_hcoded_td_id in t_objs3.hcoded_tds;

    var new_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);

    assert forall id :: id in new_objects.active_non_hcoded_tds
        ==> new_objects.active_non_hcoded_tds[id].pid != NULL;
}

lemma Lemma_DevDeactivate_BuildMap_DevsToHCodedTDVals_PreConditions(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState(k)

    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires new_dev_state.hcoded_td_id == k.subjects.devs[todeactivate_dev_id].hcoded_td_id
    requires new_dev_state.td_ids == k.subjects.devs[todeactivate_dev_id].td_ids

    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)

    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_subjects.devs[dev_id].hcoded_td_id in k'_subjects.devs[dev_id].td_ids
    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_subjects.devs[dev_id].hcoded_td_id in k'_objects.hcoded_tds
    ensures forall dev_id, td_id :: 
                dev_id in k'_subjects.devs && td_id in k'_subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k'_objects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_ProveSubjsObjsFulfillProperties(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k_cas:CAS,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_tds) <= 
                        IDToDev(k, dev_id).td_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_fds) <= 
                        IDToDev(k, dev_id).fd_ids) &&
                    (MapGetKeys(HCodedTDValOfDev(KToKParams(k).hcoded_tds, dev_id).trans_params_dos) <= 
                        IDToDev(k, dev_id).do_ids)

    requires MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)
    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)

    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires new_dev_state.pid == NULL

    requires forall o_id, dev_id :: o_id in TDIDsToObjIDs(k.subjects.devs[todeactivate_dev_id].td_ids) + 
                                            FDIDsToObjIDs(k.subjects.devs[todeactivate_dev_id].fd_ids) + 
                                            DOIDsToObjIDs(k.subjects.devs[todeactivate_dev_id].do_ids) &&
                    dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}
    requires CASGetSubjs(k_cas) == AllActiveDevs(k)
    requires CASGetObjs(k_cas) == AllActiveObjs(k)
    requires forall dev_id2 :: IsSubjInCAS(k_cas, dev_id2)
                ==> MapGetKeys<Object_ID, set<AMode>>(k_cas.m[dev_id2]) == k_cas.o_ids
        //// Requirement: The result CAS is a matrix
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> IsInCAS(k_cas, dev_id2, o_id2)
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (R in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k) &&
                                R in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
    requires forall dev_id2, o_id2 :: dev_id2 in AllActiveDevs(k) && o_id2 in AllActiveObjs(k)
                ==> (W in CASGetAModes(k_cas, dev_id2, o_id2)
                        <==> (exists tds_state2 :: tds_state2 in AllReachableActiveTDsStates(k) &&
                                W in DevAModesToObj(k, tds_state2, dev_id2, o_id2)))
        // Requirement: k_cas = BuildCAS(k, KToKParams(k), AllReachableActiveTDsStates(k))

    requires forall td_id :: td_id in k.subjects.devs[todeactivate_dev_id].td_ids
                ==> td_id.oid in AllObjsIDs(k.objects)
    requires forall fd_id :: fd_id in k.subjects.devs[todeactivate_dev_id].fd_ids
                ==> fd_id.oid in AllObjsIDs(k.objects)
    requires forall do_id :: do_id in k.subjects.devs[todeactivate_dev_id].do_ids
                ==> do_id.oid in AllObjsIDs(k.objects)
        // Requirement: Properties can be proved with other properties, but Dafny cannot easily find it

    requires forall fd_id :: fd_id in k.subjects.devs[todeactivate_dev_id].fd_ids
                ==> fd_id in k'_objects.inactive_fds
    requires forall do_id :: do_id in k.subjects.devs[todeactivate_dev_id].do_ids
                ==> do_id in k'_objects.inactive_dos
        // Requirement: FDs and DOs to be deactivated are put into <inactive_fds/dos>

    requires SubjPID_SlimState(k.subjects, todeactivate_dev_id.sid) != NULL
        // Requirement: the driver to be deactivated must be active in k
    requires forall td_id :: td_id in k.subjects.devs[todeactivate_dev_id].td_ids
                ==> ObjPID_KObjects(k.objects, td_id.oid) != NULL && ObjPID_KObjects(k'_objects, td_id.oid) == NULL
    requires forall td_id :: td_id in k.objects.hcoded_tds
                ==> k'_objects.hcoded_tds[td_id].val == k.objects.hcoded_tds[td_id].val
    requires forall td_id :: td_id in AllTDIDs(k.objects) &&
                td_id !in k.subjects.devs[todeactivate_dev_id].td_ids
            ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id)
    requires forall fd_id :: fd_id in k.subjects.devs[todeactivate_dev_id].fd_ids
                ==> ObjPID_KObjects(k.objects, fd_id.oid) != NULL && ObjPID_KObjects(k'_objects, fd_id.oid) == NULL
    requires forall fd_id :: fd_id in AllFDIDs(k.objects) &&
                fd_id !in k.subjects.devs[todeactivate_dev_id].fd_ids
            ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id)
    requires forall do_id :: do_id in k.subjects.devs[todeactivate_dev_id].do_ids
                ==> ObjPID_KObjects(k.objects, do_id.oid) != NULL && ObjPID_KObjects(k'_objects, do_id.oid) == NULL
    requires forall do_id :: do_id in AllDOIDs(k.objects) &&
                do_id !in k.subjects.devs[todeactivate_dev_id].do_ids
            ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id)

    ensures forall dev_id :: dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> dev_id in AllActiveDevs(k)
        // Property needed by the proeprties below
    ensures SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, k.subjects.devs[todeactivate_dev_id].td_ids)
    ensures SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, k.subjects.devs[todeactivate_dev_id].fd_ids)
    ensures SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, k.subjects.devs[todeactivate_dev_id].do_ids)
    ensures SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, {todeactivate_dev_id.sid}, 
                k.subjects.devs[todeactivate_dev_id].td_ids, k.subjects.devs[todeactivate_dev_id].fd_ids, k.subjects.devs[todeactivate_dev_id].do_ids)
{
    var tds_owned_by_drv:set<TD_ID> := k.subjects.devs[todeactivate_dev_id].td_ids;
    var fds_owned_by_drv:set<FD_ID> := k.subjects.devs[todeactivate_dev_id].fd_ids;
    var dos_owned_by_drv:set<DO_ID> := k.subjects.devs[todeactivate_dev_id].do_ids;

    var todeactivate_s_ids:set<Subject_ID> := {todeactivate_dev_id.sid};
    var todeactivate_td_ids := tds_owned_by_drv;
    var todeactivate_fd_ids := fds_owned_by_drv;
    var todeactivate_do_ids := dos_owned_by_drv;

    Lemma_SubjObjDeactivate_ActiveDevsInNewKHaveNoTransfersToObjsToBeDeactivated(
            k, k'_subjects, k_cas, AllReachableActiveTDsStates(k), 
            todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_DrvDevDeactivate_SubjsNotBeingDeactivatedDoNotOwnAnyObjsBeingDeactivated(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    Lemma_DrvDevDeactivate_AllObjsToBeActivatedAreActiveInK(k, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
    assert SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids);
    assert SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids);
    assert SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids);
    assert SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);
}

// [NOTE] Needs 200s to verify
lemma Lemma_DevDeactivate_ProveOtherObjectsAreUnchanged_AndTargetObjsAreDeactivated(
    k:State, dev_id:Dev_ID
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires dev_id in k.subjects.devs
    requires (forall id :: id in k.subjects.devs[dev_id].td_ids && id != k.subjects.devs[dev_id].hcoded_td_id ==> id in k.objects.active_non_hcoded_tds) &&
            (forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.active_fds) &&
            (forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.active_dos)

    ensures var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
            var todeactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
            var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
            var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
            var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
            var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);
            todeactive_hcoded_td_id in t_objs3.hcoded_tds &&

            var k'_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);

            (forall td_id :: td_id in AllTDIDs(k.objects)
                ==> (td_id in k.subjects.devs[dev_id].td_ids ==> ObjPID_KObjects(k'_objects, td_id.oid) == NULL) &&
                    (td_id !in k.subjects.devs[dev_id].td_ids ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id))) &&
            (forall fd_id :: fd_id in AllFDIDs(k.objects)
                ==> (fd_id in k.subjects.devs[dev_id].fd_ids ==> ObjPID_KObjects(k'_objects, fd_id.oid) == NULL) &&
                    (fd_id !in k.subjects.devs[dev_id].fd_ids ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id))) &&
            (forall do_id :: do_id in AllDOIDs(k.objects)
                ==> (do_id in k.subjects.devs[dev_id].do_ids ==> ObjPID_KObjects(k'_objects, do_id.oid) == NULL) &&
                    (do_id !in k.subjects.devs[dev_id].do_ids ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id)))
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    var todeactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
    var todeactive_other_td_ids := tds_owned_by_dev - {todeactive_hcoded_td_id};
    var t_objs1 := SetPIDs_ActiveNonHCodedTDs_ToNULLPID(k.objects, todeactive_other_td_ids);
    var t_objs2 := SetPIDs_ActiveFDs_ToNULLPID(t_objs1, fds_owned_by_dev);
    var t_objs3 := SetPIDs_ActiveDOs_ToNULLPID(t_objs2, dos_owned_by_dev);

    // Prove toactive_hcoded_td_id in t_objs3.hcoded_tds
    assert todeactive_hcoded_td_id in k.objects.hcoded_tds;
    assert todeactive_hcoded_td_id in t_objs3.hcoded_tds;

    var k'_objects := SetHCodedTDsPIDs(t_objs3, {todeactive_hcoded_td_id}, NULL);

    forall td_id | td_id in k.subjects.devs[dev_id].td_ids 
        ensures ObjPID_KObjects(k'_objects, td_id.oid) == NULL
    {
        assert td_id == todeactive_hcoded_td_id || td_id in todeactive_other_td_ids;
    }

    forall fd_id | fd_id in k.subjects.devs[dev_id].fd_ids 
        ensures ObjPID_KObjects(k'_objects, fd_id.oid) == NULL
    {
        // Dafny can automatically prove it
    }
}

lemma Lemma_DevDeactivate_ProveSubjsObjsFulfillProperties_PreConditions(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k_cas:CAS,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs

    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires SubjPID(k, todeactivate_dev_id.sid) != NULL
    requires new_dev_state.pid == NULL

    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)

    requires forall td_id :: td_id in AllTDIDs(k.objects)
                ==> (td_id in k.subjects.devs[todeactivate_dev_id].td_ids ==> ObjPID_KObjects(k'_objects, td_id.oid) == NULL) &&
                    (td_id !in k.subjects.devs[todeactivate_dev_id].td_ids ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id))
    requires forall fd_id :: fd_id in AllFDIDs(k.objects)
                ==> (fd_id in k.subjects.devs[todeactivate_dev_id].fd_ids ==> ObjPID_KObjects(k'_objects, fd_id.oid) == NULL) &&
                    (fd_id !in k.subjects.devs[todeactivate_dev_id].fd_ids ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id))
    requires forall do_id :: do_id in AllDOIDs(k.objects)
                ==> (do_id in k.subjects.devs[todeactivate_dev_id].do_ids ==> ObjPID_KObjects(k'_objects, do_id.oid) == NULL) &&
                    (do_id !in k.subjects.devs[todeactivate_dev_id].do_ids ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id))
    requires forall td_id :: td_id in k.objects.hcoded_tds
                ==> k'_objects.hcoded_tds[td_id].val == k.objects.hcoded_tds[td_id].val

    requires P_ObjsInSubjsAreAlsoInState(k)
    requires forall o_id, dev_id2 :: 
            (o_id in OwnObjIDs(k, todeactivate_dev_id.sid)) && 
            (dev_id2 in AllActiveDevs(k) - {todeactivate_dev_id})
            ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {}

    ensures forall o_id, dev_id :: o_id in TDIDsToObjIDs(k.subjects.devs[todeactivate_dev_id].td_ids) + 
                                            FDIDsToObjIDs(k.subjects.devs[todeactivate_dev_id].fd_ids) + 
                                            DOIDsToObjIDs(k.subjects.devs[todeactivate_dev_id].do_ids) &&
                    dev_id in AllActiveDevs_SlimState(k'_subjects)
                ==> IsInCAS(k_cas, dev_id, o_id) && CASGetAModes(k_cas, dev_id, o_id) == {}
    ensures forall td_id :: td_id in k.subjects.devs[todeactivate_dev_id].td_ids
                ==> ObjPID_KObjects(k.objects, td_id.oid) != NULL && ObjPID_KObjects(k'_objects, td_id.oid) == NULL
    ensures forall td_id :: td_id in AllTDIDs(k.objects) &&
                td_id !in k.subjects.devs[todeactivate_dev_id].td_ids
            ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id)
    ensures forall fd_id :: fd_id in k.subjects.devs[todeactivate_dev_id].fd_ids
                ==> ObjPID_KObjects(k.objects, fd_id.oid) != NULL && ObjPID_KObjects(k'_objects, fd_id.oid) == NULL
    ensures forall fd_id :: fd_id in AllFDIDs(k.objects) &&
                fd_id !in k.subjects.devs[todeactivate_dev_id].fd_ids
            ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id)
    ensures forall do_id :: do_id in k.subjects.devs[todeactivate_dev_id].do_ids
                ==> ObjPID_KObjects(k.objects, do_id.oid) != NULL && ObjPID_KObjects(k'_objects, do_id.oid) == NULL
    ensures forall do_id :: do_id in AllDOIDs(k.objects) &&
                do_id !in k.subjects.devs[todeactivate_dev_id].do_ids
            ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id)
{
    forall td_id | td_id in k.subjects.devs[todeactivate_dev_id].td_ids
        ensures ObjPID_KObjects(k.objects, td_id.oid) != NULL
    {
        assert DoOwnObj(k, todeactivate_dev_id.sid, td_id.oid);
    }
    forall fd_id | fd_id in k.subjects.devs[todeactivate_dev_id].fd_ids
        ensures ObjPID_KObjects(k.objects, fd_id.oid) != NULL
    {
        assert DoOwnObj(k, todeactivate_dev_id.sid, fd_id.oid);
    }
    forall do_id | do_id in k.subjects.devs[todeactivate_dev_id].do_ids
        ensures ObjPID_KObjects(k.objects, do_id.oid) != NULL
    {
        assert DoOwnObj(k, todeactivate_dev_id.sid, do_id.oid);
    }
}

lemma Lemma_DevDeactivate_ActiveDevsInNewKIsActiveDevsInKMinusDevToBeDeactivated(
    k:State, k'_subjects:Subjects,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState(k)
    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires SubjPID(k, todeactivate_dev_id.sid) != NULL
    requires new_dev_state.pid == NULL

    ensures AllActiveDevs_SlimState(k'_subjects) == AllActiveDevs(k) - {todeactivate_dev_id}
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_OwnershipOfObjsIsPreserved(
    k:State, k'_subjects:Subjects,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires new_dev_state.hcoded_td_id == IDToDev(k, todeactivate_dev_id).hcoded_td_id
    requires new_dev_state.td_ids == IDToDev(k, todeactivate_dev_id).td_ids
    requires new_dev_state.fd_ids == IDToDev(k, todeactivate_dev_id).fd_ids
    requires new_dev_state.do_ids == IDToDev(k, todeactivate_dev_id).do_ids

    ensures forall drv_id :: drv_id in k'_subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_HCodedTDsHaveUnmodifiedVals(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)

    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires forall td_id :: td_id in k.objects.hcoded_tds
                ==> k'_objects.hcoded_tds[td_id].val == k.objects.hcoded_tds[td_id].val

    requires new_dev_state.hcoded_td_id == k.subjects.devs[todeactivate_dev_id].hcoded_td_id

    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val == k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_UnchangedStateVarsBetweenKandNewK(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires todeactivate_dev_id in k.subjects.devs
    requires k'_subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires new_dev_state.hcoded_td_id == k.subjects.devs[todeactivate_dev_id].hcoded_td_id
    requires new_dev_state.td_ids == k.subjects.devs[todeactivate_dev_id].td_ids
    requires new_dev_state.fd_ids == k.subjects.devs[todeactivate_dev_id].fd_ids
    requires new_dev_state.do_ids == k.subjects.devs[todeactivate_dev_id].do_ids

    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)
    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)

    ensures SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevDeactivate_ProveIsValidState_Subjects(
    k:State, k':State,
    todeactivate_dev_id:Dev_ID, new_dev_state:Dev_State
)
    requires IsValidState_Subjects(k)
    requires todeactivate_dev_id in k.subjects.devs
    requires k'.subjects == Subjects(k.subjects.drvs, k.subjects.devs[todeactivate_dev_id := new_dev_state])

    requires MapGetKeys(k'.subjects.drvs) == MapGetKeys(k.subjects.drvs)
    requires MapGetKeys(k'.subjects.devs) == MapGetKeys(k.subjects.devs)

    ensures IsValidState_Subjects(k')
{
    // Dafny can automatically prove this lemma
}




//******** Private Lemmas  ********//
lemma Lemma_SubjObjDeactivate_NewK_ActiveObjsInNewKHasUnchangedPIDs(
    k:State, k':State,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures forall o_id :: o_id in AllActiveObjs(k')
                ==> ObjPID(k, o_id) == ObjPID(k', o_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjDeactivate_NewK_ReachableActiveTDsStatesInK_FulfillConditionsToObjsBeingDeactivated(
    k:State, k':State,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToTDsBeingDeactivated(k, k', todeactivate_td_ids)
    ensures SubjObjDeactivate_ReachableActiveTDsStatesInK_FulfillConditionsToFDsAndDOsBeingDeactivated(
                k, k', todeactivate_fd_ids, todeactivate_do_ids)
{
    // Dafny can automatically prove this lemma
}

// (needs 200s to verify)
lemma Lemma_SubjObjDeactivate_NewK_FulfillNextThreePredicates(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    todeactivate_s_ids:set<Subject_ID>, todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjDeactivate_PreConditionsOfK(k)
    requires SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures SubjObjDeactivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    ensures CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    ensures SubjObjDeactivate_PreConditionsOfK(k')
{
    assert forall td_id2 :: td_id2 in k_params.all_active_tds
                <==> td_id2 in k_params.objs_td_ids &&
                    ObjPID_SlimState(k_params.objs_pids, td_id2.oid) != NULL by
    {
        Lemma_KToKParams_Properties(k, k_params);
    }

    // Prove P_ObjsInSubjsAreAlsoInState(k')
    assert P_ObjsInSubjsAreAlsoInState(k');
}

lemma Lemma_SubjObjDeactivate_NewK_PreConditionsOfSubjObjToDeactivate(
    k:State, k':State, todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k') 

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, AllTDIDs(k'.objects), AllFDIDs(k'.objects), AllDOIDs(k'.objects))
    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures SubjObjDeactivate_PreConditionsOfK(k)
    ensures SubjObjDeactivate_PreConditionsOfSubjObjToDeactivate(k, k', todeactivate_s_ids, todeactivate_td_ids)
{
    Lemma_AllActiveObjs_SlimState_Property(k.objects);

    forall drv_id2:Drv_ID | IsDrvID(k, drv_id2) &&
                    drv_id2.sid !in todeactivate_s_ids
        ensures k'.subjects.drvs[drv_id2] == k.subjects.drvs[drv_id2]
    {
        assert drv_id2.sid in AllSubjsIDs(k.subjects);
        assert drv_id2 in k.subjects.drvs;
    }

    // Prove AllActiveTDs(k') == AllActiveTDs(k) - todeactivate_td_ids
    Lemma_SubjObjDeactivate_NewK_PreConditionsOfSubjObjToDeactivate_ProveRelationshipOfActiveTDs(k, k', todeactivate_td_ids);
    assert AllActiveTDs(k') == AllActiveTDs(k) - todeactivate_td_ids;

    Lemma_K_ValidStateFulfillUniqueIDsAndOwnedObjs(k);
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);
}

lemma Lemma_SubjObjDeactivate_NewK_PreConditionsOfSubjObjToDeactivate_ProveRelationshipOfActiveTDs(
    k:State, k':State, todeactivate_td_ids:set<TD_ID>
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires IsValidState_Subjects(k) && IsValidState_Objects(k)
    requires MapGetKeys(k'.objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires MapGetKeys(k.objects.hcoded_tds) == AllHCodedTDIDs(k.subjects)
    requires forall dev_id :: dev_id in AllActiveDevs_SlimState(k'.subjects)
                ==> dev_id in AllActiveDevs(k)

    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)

    ensures AllActiveTDs(k') == AllActiveTDs(k) - todeactivate_td_ids
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjDeactivate_NewK_SubjsObjsPIDsInNewK(
    k:State, k':State, todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k') 

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, AllTDIDs(k'.objects), AllFDIDs(k'.objects), AllDOIDs(k'.objects))
    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures IsValidState_SubjsOwnObjsThenInSamePartition(k')
    ensures SubjObjDeactivate_SubjsObjsPIDsInNewK(k')
{
    Lemma_SubjObjDeactivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition(
        k, k', todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids);

    forall dev_id | dev_id in k'.subjects.devs
        ensures forall td_id :: td_id in IDToDev(k', dev_id).td_ids
                    ==> ObjPID(k', td_id.oid) == SubjPID(k', dev_id.sid)
        ensures forall fd_id :: fd_id in IDToDev(k', dev_id).fd_ids
                    ==> ObjPID(k', fd_id.oid) == SubjPID(k', dev_id.sid)
        ensures forall do_id :: do_id in IDToDev(k', dev_id).do_ids
                    ==> ObjPID(k', do_id.oid) == SubjPID(k', dev_id.sid)
    {
        assert dev_id.sid in AllSubjsIDs(k'.subjects);
        assert forall td_id :: td_id in IDToDev(k', dev_id).td_ids
                    ==> DoOwnObj(k', dev_id.sid, td_id.oid);
        assert forall fd_id :: fd_id in IDToDev(k', dev_id).fd_ids
                    ==> DoOwnObj(k', dev_id.sid, fd_id.oid);
        assert forall do_id :: do_id in IDToDev(k', dev_id).do_ids
                    ==> DoOwnObj(k', dev_id.sid, do_id.oid);
    }
}

lemma Lemma_SubjObjDeactivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition(
    k:State, k':State, todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK(k, k') 

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, AllTDIDs(k'.objects), AllFDIDs(k'.objects), AllDOIDs(k'.objects))
    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'.subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'.subjects, k'.objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'.subjects, k'.objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'.subjects, k'.objects, todeactivate_do_ids)

    ensures IsValidState_SubjsOwnObjsThenInSamePartition(k')
{
    forall s_id, o_id | s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id)
        ensures SubjPID(k', s_id) == ObjPID(k', o_id)
    {
        if(s_id !in todeactivate_s_ids)
        {
            assert DoOwnObj(k, s_id, o_id);
            Lemma_SubjObjDeactivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition_Private(
                k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, s_id, o_id);
            assert TD_ID(o_id) !in todeactivate_td_ids;
            assert FD_ID(o_id) !in todeactivate_fd_ids;
            assert DO_ID(o_id) !in todeactivate_do_ids;

            if(Drv_ID(s_id) in k.subjects.drvs)
            {
                assert SubjPID_SlimState(k'.subjects, s_id) == k.subjects.drvs[Drv_ID(s_id)].pid;

                assert ObjPID(k', o_id) == ObjPID(k, o_id);
                assert SubjPID(k', s_id) == ObjPID(k', o_id);
            }
            else
            {
                assert Dev_ID(s_id) in k.subjects.devs;

                assert ObjPID(k', o_id) == ObjPID(k, o_id);
                assert SubjPID(k', s_id) == ObjPID(k', o_id);
            }
        }
        else
        {
            assert s_id in todeactivate_s_ids;

            assert SubjPID_SlimState(k'.subjects, s_id) == NULL;
            if(Drv_ID(s_id) in k.subjects.drvs)
            {
                assert TD_ID(o_id) in todeactivate_td_ids || 
                       FD_ID(o_id) in todeactivate_fd_ids ||
                       DO_ID(o_id) in todeactivate_do_ids;

                assert ObjPID(k', o_id) == NULL;
            }
            else
            {
                assert Dev_ID(s_id) in k.subjects.devs;
                assert TD_ID(o_id) in todeactivate_td_ids || 
                       FD_ID(o_id) in todeactivate_fd_ids ||
                       DO_ID(o_id) in todeactivate_do_ids;

                assert ObjPID(k', o_id) == NULL;
            }
        }
    }
}

lemma Lemma_SubjObjDeactivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition_Private(
    k:State,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k)

    requires todeactivate_td_ids <= AllTDIDs(k.objects)
    requires todeactivate_fd_ids <= AllFDIDs(k.objects)
    requires todeactivate_do_ids <= AllDOIDs(k.objects)

    requires s_id in AllSubjsIDs(k.subjects)

    requires OwnedTDs(k, s_id) * todeactivate_td_ids == {}
    requires OwnedFDs(k, s_id) * todeactivate_fd_ids == {}
    requires OwnedDOs(k, s_id) * todeactivate_do_ids == {}

    requires DoOwnObj(k, s_id, o_id)

    ensures TD_ID(o_id) !in todeactivate_td_ids
    ensures FD_ID(o_id) !in todeactivate_fd_ids
    ensures DO_ID(o_id) !in todeactivate_do_ids 
{
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(OwnedTDs(k, s_id), todeactivate_td_ids);
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(OwnedFDs(k, s_id), todeactivate_fd_ids);
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(OwnedDOs(k, s_id), todeactivate_do_ids);
}

lemma Lemma_DrvDevDeactivate_AllObjsToBeActivatedAreActiveInK(
    k:State, todeactivate_s_ids:set<Subject_ID>,
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)

    requires todeactivate_s_ids <= AllSubjsIDs(k.subjects)
    requires forall s_id :: s_id in todeactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) != NULL
        // Requirement: All subjects to be activated are inactive in k 
    requires forall td_id :: td_id in todeactivate_td_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in todeactivate_fd_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in todeactivate_do_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    ensures forall td_id :: td_id in todeactivate_td_ids
            ==> ObjPID_KObjects(k.objects, td_id.oid) != NULL
    ensures forall fd_id :: fd_id in todeactivate_fd_ids
            ==> ObjPID_KObjects(k.objects, fd_id.oid) != NULL
    ensures forall do_id :: do_id in todeactivate_do_ids
            ==> ObjPID_KObjects(k.objects, do_id.oid) != NULL
{
    forall td_id | td_id in todeactivate_td_ids
        ensures ObjPID_KObjects(k.objects, td_id.oid) != NULL
    {
        assert exists s_id :: s_id in todeactivate_s_ids && DoOwnObj(k, s_id, td_id.oid);
        assert ObjPID_KObjects(k.objects, td_id.oid) != NULL;
    }

    forall fd_id | fd_id in todeactivate_fd_ids
        ensures ObjPID_KObjects(k.objects, fd_id.oid) != NULL
    {
        assert exists s_id :: s_id in todeactivate_s_ids && DoOwnObj(k, s_id, fd_id.oid);
        assert ObjPID_KObjects(k.objects, fd_id.oid) != NULL;
    }

    forall do_id | do_id in todeactivate_do_ids
        ensures ObjPID_KObjects(k.objects, do_id.oid) != NULL
    {
        assert exists s_id :: s_id in todeactivate_s_ids && DoOwnObj(k, s_id, do_id.oid);
        assert ObjPID_KObjects(k.objects, do_id.oid) != NULL;
    }
}

lemma Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs_OwnedObjsAreInNewK(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids)

    requires k'_params == ReachableTDsKParams(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects))

    ensures forall s_id, o_id :: s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
                ==> o_id in k'_params.objs_pids
{
    forall s_id, o_id | s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
        ensures o_id in k'_params.objs_pids
    {
        assert IsSubjID(k.subjects, s_id);
        assert o_id in AllObjsIDs(k'_objects);
        assert MapGetKeys(BuildMap_ObjIDsToPIDs(k'_objects)) == AllObjsIDs(k'_objects);
        assert k'_params.objs_pids == BuildMap_ObjIDsToPIDs(k'_objects);
        assert o_id in k'_params.objs_pids;
    }
}

lemma Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsBeingDeactivated(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids)

    requires IsSubjID(k.subjects, s_id)
    requires s_id in todeactivate_s_ids
        // Requirement: The subject (<s_id>) is not being activated

    requires k'_params == ReachableTDsKParams(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects))
    requires DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)

    requires o_id in k'_params.objs_pids

    ensures k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
{
    assert TD_ID(o_id) in todeactivate_td_ids || FD_ID(o_id) in todeactivate_fd_ids || DO_ID(o_id) in todeactivate_do_ids;
    assert k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id);
}

lemma Lemma_DrvDevDeactivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsNotBeingDeactivated(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires todeactivate_s_ids <= AllSubjsIDs(k.subjects) 
    requires forall td_id :: td_id in todeactivate_td_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in todeactivate_fd_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in todeactivate_do_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    requires SubjObjDeactivate_PropertiesOfSubjs(k, k'_subjects, todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids)
    requires SubjObjDeactivate_PropertiesOfTDs(k, k'_subjects, k'_objects, todeactivate_td_ids)
    requires SubjObjDeactivate_PropertiesOfFDs(k, k'_subjects, k'_objects, todeactivate_fd_ids)
    requires SubjObjDeactivate_PropertiesOfDOs(k, k'_subjects, k'_objects, todeactivate_do_ids)

    requires IsSubjID(k.subjects, s_id)
    requires s_id !in todeactivate_s_ids
        // Requirement: The subject (<s_id>) is not being activated

    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_subjects.devs[dev_id].hcoded_td_id in k'_subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k'_subjects.devs && td_id in k'_subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k'_objects) 

    requires k'_params == ReachableTDsKParams(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects))
    requires DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)

    requires o_id in k'_params.objs_pids

    ensures k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
{
    Lemma_DrvDevDeactivate_InSubjsNotBeingDeactivated_ObjsAreUnchanged(k, k'_subjects, k'_objects, k'_params, 
        todeactivate_s_ids, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, s_id, o_id);
    assert TD_ID(o_id) !in todeactivate_td_ids && FD_ID(o_id) !in todeactivate_fd_ids && DO_ID(o_id) !in todeactivate_do_ids;

    Lemma_SameObjsOwnershipInSuccessiveStates_SlimState(k, k'_subjects, k'_objects);
    if(TD_ID(o_id) in AllTDIDs(k.objects))
    {
        //assert k'_objects.tds[TD_ID(o_id)] == k.objects.tds[TD_ID(o_id)];
        assert ObjPID_KObjects(k.objects, o_id) == ObjPID(k, o_id);
        assert ObjPID_KObjects(k.objects, o_id) == SubjPID(k, s_id);
        assert k'_params.objs_pids[o_id] == ObjPID_KObjects(k'_objects, o_id);

        assert k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id);
    }

    if(FD_ID(o_id) in AllFDIDs(k.objects))
    {
        //assert k'_objects.fds[FD_ID(o_id)] == k.objects.fds[FD_ID(o_id)];
        assert ObjPID_KObjects(k.objects, o_id) == ObjPID(k, o_id);
        assert ObjPID_KObjects(k.objects, o_id) == SubjPID(k, s_id);
        assert k'_params.objs_pids[o_id] == ObjPID_KObjects(k'_objects, o_id);

        assert k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id);
    }

    if(DO_ID(o_id) in AllDOIDs(k.objects))
    {
        //assert k'_objects.dos[DO_ID(o_id)] == k.objects.dos[DO_ID(o_id)];
        assert ObjPID_KObjects(k.objects, o_id) == ObjPID(k, o_id);
        assert ObjPID_KObjects(k.objects, o_id) == SubjPID(k, s_id);
        assert k'_params.objs_pids[o_id] == ObjPID_KObjects(k'_objects, o_id);

        assert k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id);
    }
}

lemma Lemma_DrvDevDeactivate_InSubjsNotBeingDeactivated_ObjsAreUnchanged(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    todeactivate_s_ids:set<Subject_ID>, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjDeactivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects) 

    requires todeactivate_s_ids <= AllSubjsIDs(k.subjects) 
    requires forall td_id :: td_id in todeactivate_td_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in todeactivate_fd_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in todeactivate_do_ids
            ==> (exists s_id :: s_id in todeactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    requires IsSubjID(k.subjects, s_id)
    requires s_id !in todeactivate_s_ids
        // Requirement: The subject (<s_id>) is not being activated
  
    requires k'_params == ReachableTDsKParams(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects))
    requires DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)

    ensures TD_ID(o_id) !in todeactivate_td_ids && FD_ID(o_id) !in todeactivate_fd_ids && DO_ID(o_id) !in todeactivate_do_ids
{
    assert forall o_id, s_id1, s_id2 :: 
        s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
        DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
        ==> s_id1 == s_id2;

    Lemma_SameObjsOwnershipInSuccessiveStates_SlimState(k, k'_subjects, k'_objects);
    if(TD_ID(o_id) in todeactivate_td_ids)
    {
        assert exists s_id2 :: s_id2 in todeactivate_s_ids && TD_ID(o_id) in OwnedTDs(k, s_id2);
        var s_id2 :| s_id2 in todeactivate_s_ids && TD_ID(o_id) in OwnedTDs(k, s_id2);
        assert DoOwnObj(k, s_id2, o_id);

        assert DoOwnObj_SlimState(k'_subjects, s_id, o_id);
        assert DoOwnObj(k, s_id, o_id);

        // Show conflict
        assert s_id2 == s_id;
        assert s_id2 !in todeactivate_s_ids;
    }

    if(FD_ID(o_id) in todeactivate_fd_ids)
    {
        assert exists s_id2 :: s_id2 in todeactivate_s_ids && FD_ID(o_id) in OwnedFDs(k, s_id2);
        var s_id2 :| s_id2 in todeactivate_s_ids && FD_ID(o_id) in OwnedFDs(k, s_id2);
        assert DoOwnObj(k, s_id2, o_id);

        assert DoOwnObj_SlimState(k'_subjects, s_id, o_id);
        assert DoOwnObj(k, s_id, o_id);

        // Show conflict
        assert s_id2 == s_id;
        assert s_id2 !in todeactivate_s_ids;
    }

    if(DO_ID(o_id) in todeactivate_do_ids)
    {
        assert exists s_id2 :: s_id2 in todeactivate_s_ids && DO_ID(o_id) in OwnedDOs(k, s_id2);
        var s_id2 :| s_id2 in todeactivate_s_ids && DO_ID(o_id) in OwnedDOs(k, s_id2);
        assert DoOwnObj(k, s_id2, o_id);

        assert DoOwnObj_SlimState(k'_subjects, s_id, o_id);
        assert DoOwnObj(k, s_id, o_id);

        // Show conflict
        assert s_id2 == s_id;
        assert s_id2 !in todeactivate_s_ids;
    }
}

lemma Lemma_DevDeactivate_NoTransferToDevToBeDeactivated_Equivilant(
    k:State, dev_sid:Subject_ID, k_cas:CAS, tds_states_set:set<TDs_Vals>
)
    requires IsValidState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
    requires tds_states_set == AllReachableActiveTDsStates(k)
    
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas)
        // Property of BuildCAS
    
    ensures P_ObjsInSubjsAreAlsoInState(k)
    ensures (forall o_id, dev_id2 :: 
                (o_id in OwnObjIDs(k, dev_sid)) && 
                (dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)})
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
            <==>
            (forall o_id, dev_id2 :: o_id in OwnObjIDs(k, dev_sid) && 
                        dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)}
                    ==> (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
{
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);

    if(forall o_id, dev_id2 :: 
                (o_id in OwnObjIDs(k, dev_sid)) && 
                (dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)})
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
    {
        forall o_id, dev_id2 | o_id in OwnObjIDs(k, dev_sid) && 
                        dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)}
            ensures forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}
        {
            assert IsInCAS(k_cas, dev_id2, o_id);
            assert CASGetAModes(k_cas, dev_id2, o_id) == {};

            assert dev_id2 in AllActiveDevs(k) && o_id in AllActiveObjs(k);
            if(exists tds_state2 :: tds_state2 in tds_states_set && 
                    DevAModesToObj(k, tds_state2, dev_id2, o_id) != {})
            {
                var tds_state2 :| tds_state2 in tds_states_set && 
                    DevAModesToObj(k, tds_state2, dev_id2, o_id) != {};

                AllReqNonEmptyAModesMustContainROrW();
                assert R in DevAModesToObj(k, tds_state2, dev_id2, o_id) ||
                       W in DevAModesToObj(k, tds_state2, dev_id2, o_id);

                assert R in CASGetAModes(k_cas, dev_id2, o_id) || W in  CASGetAModes(k_cas, dev_id2, o_id);
                IfAModesContainROrWThenNotEmpty();
                assert CASGetAModes(k_cas, dev_id2, o_id) != {};
            }
        }
    }

    if(forall o_id, dev_id2 :: o_id in OwnObjIDs(k, dev_sid) && 
                        dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)}
                    ==> (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
    {
        forall o_id, dev_id2 |(o_id in OwnObjIDs(k, dev_sid)) &&
                (dev_id2 in AllActiveDevs(k) - {Dev_ID(dev_sid)})
            ensures IsInCAS(k_cas, dev_id2, o_id) 
            ensures CASGetAModes(k_cas, dev_id2, o_id) == {}
        {
            assert dev_id2 in AllActiveDevs(k);

            assert IsValidState_SubjsOwnObjsThenInSamePartition(k);
            Lemma_OwnObjIDs_Property(k, dev_sid);
            assert DoOwnObj(k, dev_sid, o_id);
            assert ObjPID(k, o_id) != NULL;
            assert o_id in AllActiveObjs(k);

            assert IsInCAS(k_cas, dev_id2, o_id);

            assert (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {});
            if(CASGetAModes(k_cas, dev_id2, o_id) != {})
            {
                AllReqNonEmptyAModesMustContainROrW();
                assert R in CASGetAModes(k_cas, dev_id2, o_id) || W in CASGetAModes(k_cas, dev_id2, o_id);

                assert (exists tds_state2 :: tds_state2 in tds_states_set && R in DevAModesToObj(k, tds_state2, dev_id2, o_id)) ||
                       (exists tds_state2 :: tds_state2 in tds_states_set && W in DevAModesToObj(k, tds_state2, dev_id2, o_id));
                IfAModesContainROrWThenNotEmpty();
                assert exists tds_state2 :: tds_state2 in tds_states_set && DevAModesToObj(k, tds_state2, dev_id2, o_id) != {};
            }
        }
    }
}

lemma Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant(
    k:State, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_cas:CAS, tds_states_set:set<TDs_Vals>
)
    requires IsValidState(k)
    requires tds_states_set == AllReachableActiveTDsStates(k)

    requires forall id :: id in todeactivate_td_ids 
                ==> id in AllTDIDs(k.objects)
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in AllFDIDs(k.objects)
    requires forall id :: id in todeactivate_do_ids 
                ==> id in AllDOIDs(k.objects)

    requires forall id :: id in todeactivate_td_ids 
                ==> ObjPID(k, id.oid) != NULL
    requires forall id :: id in todeactivate_fd_ids 
                ==> ObjPID(k, id.oid) != NULL
    requires forall id :: id in todeactivate_do_ids 
                ==> ObjPID(k, id.oid) != NULL
    
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas)
        // Property of BuildCAS
    
    ensures P_ObjsInSubjsAreAlsoInState(k)
    ensures (forall o_id, dev_id2 :: 
                (o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)) && 
                (dev_id2 in AllActiveDevs(k))
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
            <==>
            (forall o_id, dev_id2 :: o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids) && 
                        dev_id2 in AllActiveDevs(k)
                    ==> (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
{
    Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant_Right(
        k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas, tds_states_set);
    Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant_Left(
        k, todeactivate_td_ids, todeactivate_fd_ids, todeactivate_do_ids, k_cas, tds_states_set);
}

// (needs 30s to verify)
lemma Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant_Right(
    k:State, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_cas:CAS, tds_states_set:set<TDs_Vals>
)
    requires IsValidState(k)
    requires tds_states_set == AllReachableActiveTDsStates(k)

    requires forall id :: id in todeactivate_td_ids 
                ==> id in AllTDIDs(k.objects)
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in AllFDIDs(k.objects)
    requires forall id :: id in todeactivate_do_ids 
                ==> id in AllDOIDs(k.objects)
    
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas)
        // Property of BuildCAS
    
    ensures P_ObjsInSubjsAreAlsoInState(k)
    ensures (forall o_id, dev_id2 :: 
                (o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)) && 
                (dev_id2 in AllActiveDevs(k))
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
            ==>
            (forall o_id, dev_id2 :: o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids) && 
                        dev_id2 in AllActiveDevs(k)
                    ==> (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
{
    var all_objs_todeactivate := TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids);
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);

    if(forall o_id, dev_id2 :: 
                (o_id in all_objs_todeactivate) && 
                (dev_id2 in AllActiveDevs(k))
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
    {
        forall o_id, dev_id2 | o_id in all_objs_todeactivate && 
                        dev_id2 in AllActiveDevs(k)
            ensures forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}
        {
            assert IsInCAS(k_cas, dev_id2, o_id);
            assert CASGetAModes(k_cas, dev_id2, o_id) == {};

            assert dev_id2 in AllActiveDevs(k) && o_id in AllActiveObjs(k);
            if(exists tds_state2 :: tds_state2 in tds_states_set && 
                    DevAModesToObj(k, tds_state2, dev_id2, o_id) != {})
            {
                var tds_state2 :| tds_state2 in tds_states_set && 
                    DevAModesToObj(k, tds_state2, dev_id2, o_id) != {};

                AllReqNonEmptyAModesMustContainROrW();
                assert R in DevAModesToObj(k, tds_state2, dev_id2, o_id) ||
                       W in DevAModesToObj(k, tds_state2, dev_id2, o_id);

                assert R in CASGetAModes(k_cas, dev_id2, o_id) || W in  CASGetAModes(k_cas, dev_id2, o_id);
                IfAModesContainROrWThenNotEmpty();
                assert CASGetAModes(k_cas, dev_id2, o_id) != {};
            }
        }
    }
}

// [NOTE] needs 100s to verify
lemma Lemma_ObjsDeactivate_NoTransferToObjsToBeDeactivated_Equivilant_Left(
    k:State, 
    todeactivate_td_ids:set<TD_ID>, todeactivate_fd_ids:set<FD_ID>, todeactivate_do_ids:set<DO_ID>,
    k_cas:CAS, tds_states_set:set<TDs_Vals>
)
    requires IsValidState(k)
    requires tds_states_set == AllReachableActiveTDsStates(k)

    requires forall id :: id in todeactivate_td_ids 
                ==> id in AllTDIDs(k.objects)
    requires forall id :: id in todeactivate_fd_ids 
                ==> id in AllFDIDs(k.objects)
    requires forall id :: id in todeactivate_do_ids 
                ==> id in AllDOIDs(k.objects)

    requires forall id :: id in todeactivate_td_ids 
                ==> ObjPID(k, id.oid) != NULL
    requires forall id :: id in todeactivate_fd_ids 
                ==> ObjPID(k, id.oid) != NULL
    requires forall id :: id in todeactivate_do_ids 
                ==> ObjPID(k, id.oid) != NULL
    
    requires P_BuildCAS_Properties(k, tds_states_set, k_cas)
        // Property of BuildCAS
    
    ensures P_ObjsInSubjsAreAlsoInState(k)
    ensures (forall o_id, dev_id2 :: 
                (o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids)) && 
                (dev_id2 in AllActiveDevs(k))
                ==> IsInCAS(k_cas, dev_id2, o_id) && CASGetAModes(k_cas, dev_id2, o_id) == {})
            <==
            (forall o_id, dev_id2 :: o_id in TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids) && 
                        dev_id2 in AllActiveDevs(k)
                    ==> (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
{
    var all_objs_todeactivate := TDIDsToObjIDs(todeactivate_td_ids) + FDIDsToObjIDs(todeactivate_fd_ids) + DOIDsToObjIDs(todeactivate_do_ids);
    Lemma_P_ObjsInSubjsAreAlsoInState_Prove(k);

    if(forall o_id, dev_id2 :: o_id in all_objs_todeactivate && 
                        dev_id2 in AllActiveDevs(k)
                    ==> (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {}))
    {
        forall o_id, dev_id2 |(o_id in all_objs_todeactivate) &&
                (dev_id2 in AllActiveDevs(k))
            ensures IsInCAS(k_cas, dev_id2, o_id) 
            ensures CASGetAModes(k_cas, dev_id2, o_id) == {}
        {
            assert dev_id2 in AllActiveDevs(k);

            assert ObjPID(k, o_id) != NULL;
            assert o_id in AllActiveObjs(k);

            assert IsInCAS(k_cas, dev_id2, o_id);

            assert (forall tds_state2 :: tds_state2 in tds_states_set
                            ==> DevAModesToObj(k, tds_state2, dev_id2, o_id) == {});
            if(CASGetAModes(k_cas, dev_id2, o_id) != {})
            {
                AllReqNonEmptyAModesMustContainROrW();
                assert R in CASGetAModes(k_cas, dev_id2, o_id) || W in CASGetAModes(k_cas, dev_id2, o_id);

                assert (exists tds_state2 :: tds_state2 in tds_states_set && R in DevAModesToObj(k, tds_state2, dev_id2, o_id)) ||
                       (exists tds_state2 :: tds_state2 in tds_states_set && W in DevAModesToObj(k, tds_state2, dev_id2, o_id));
                IfAModesContainROrWThenNotEmpty();
                assert exists tds_state2 :: tds_state2 in tds_states_set && DevAModesToObj(k, tds_state2, dev_id2, o_id) != {};
            }
        }
    }
}