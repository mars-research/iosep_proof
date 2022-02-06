include "Syntax.dfy"
include "Properties.dfy"
include "Utils.dfy"
include "CASOps.dfy"
include "Lemmas.dfy"
include "Lemmas_Ops.dfy"
include "Lemmas_SubjActivate_ReachableTDsStates.dfy"

predicate SubjObjActivate_PropertiesOfNewTDs(k:State, k'_objects:Objects, toactivate_td_ids:set<TD_ID>, pid:Partition_ID)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires MapGetKeys(k.objects.hcoded_tds) == AllHCodedTDIDs(k.subjects)
{
    var hcoded_td_ids := AllHCodedTDIDs(k.subjects);
    var toactivate_hcoded_td_ids := set td_id | td_id in hcoded_td_ids && td_id in toactivate_td_ids :: td_id;

    (AllTDIDs(k'_objects) == AllTDIDs(k.objects)) &&
    (toactivate_td_ids <= AllTDIDs(k.objects)) &&
    (forall td_id :: td_id in toactivate_td_ids
            ==> ObjPID_KObjects(k.objects, td_id.oid) == NULL) &&
    (forall td_id :: td_id in toactivate_td_ids
            ==> ObjPID_KObjects(k'_objects, td_id.oid) == pid) &&

    (toactivate_hcoded_td_ids <= toactivate_td_ids) &&
    (forall td_id :: td_id in toactivate_td_ids &&
                td_id !in toactivate_hcoded_td_ids
            ==> td_id in k'_objects.active_non_hcoded_tds &&
                k'_objects.active_non_hcoded_tds[td_id].val == TD_Val(map[], map[], map[])) &&
    (forall td_id :: td_id in toactivate_hcoded_td_ids
            ==> k'_objects.hcoded_tds[td_id].val == k.objects.hcoded_tds[td_id].val) &&
        // Forall TDs to be activated, hardcoded TDs preserve their values,
        // and other TDs are cleared

    (forall td_id :: td_id in AllTDIDs(k.objects) &&
                td_id !in toactivate_td_ids
            ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id)
    ) &&

    (true)
}

predicate SubjObjActivate_PropertiesOfNewFDs(k:State, k'_objects:Objects, toactivate_fd_ids:set<FD_ID>, pid:Partition_ID)
{
    (AllFDIDs(k'_objects) == AllFDIDs(k.objects)) &&
    (toactivate_fd_ids <= AllFDIDs(k.objects)) &&
    (forall fd_id :: fd_id in toactivate_fd_ids
            ==> fd_id in k.objects.inactive_fds
    ) &&
    (forall fd_id :: fd_id in toactivate_fd_ids
            ==> fd_id in k'_objects.active_fds &&
            k'_objects.active_fds[fd_id].pid == pid
    ) &&
    (forall fd_id :: fd_id in toactivate_fd_ids
            ==> k'_objects.active_fds[fd_id].val == FD_Val("")
    ) &&
    (forall fd_id :: fd_id in AllFDIDs(k.objects) &&
                fd_id !in toactivate_fd_ids
            ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id)
    ) &&

    (true)
}

predicate SubjObjActivate_PropertiesOfNewDOs(k:State, k'_objects:Objects, toactivate_do_ids:set<DO_ID>, pid:Partition_ID)
{
    (AllDOIDs(k'_objects) == AllDOIDs(k.objects)) &&
    (toactivate_do_ids <= AllDOIDs(k.objects)) &&
    (forall do_id :: do_id in toactivate_do_ids
            ==> do_id in k.objects.inactive_dos
    ) &&
    (forall do_id :: do_id in toactivate_do_ids
            ==> do_id in k'_objects.active_dos &&
            k'_objects.active_dos[do_id].pid == pid
    ) &&
    (forall do_id :: do_id in toactivate_do_ids
            ==> k'_objects.active_dos[do_id].val == DO_Val("")
    ) &&
    (forall do_id :: do_id in AllDOIDs(k.objects) &&
                do_id !in toactivate_do_ids
            ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id)
    ) &&

    (true)
}

predicate SubjObjActivate_PropertiesOfNewSubjs(
    k:State, k'_subjects:Subjects, toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)
{
    (AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)) &&
    (MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)) &&
    (MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)) &&

    (toactivate_s_ids <= AllSubjsIDs(k.subjects)) &&
    (forall s_id :: s_id in toactivate_s_ids 
                ==> OwnedTDs(k, s_id) <= toactivate_td_ids &&
                    OwnedFDs(k, s_id) <= toactivate_fd_ids &&
                    OwnedDOs(k, s_id) <= toactivate_do_ids) &&
        // If a subject is to be activated, then its objects are also to be activated
    (forall s_id :: s_id in toactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) == NULL) &&
    (forall s_id :: s_id in toactivate_s_ids
            ==> SubjPID_SlimState(k'_subjects, s_id) == pid) &&

    (forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in toactivate_s_ids
            ==> (Drv_ID(s_id) in k.subjects.drvs ==> k'_subjects.drvs[Drv_ID(s_id)] == k.subjects.drvs[Drv_ID(s_id)]) &&
                (Dev_ID(s_id) in k.subjects.devs ==> k'_subjects.devs[Dev_ID(s_id)] == k.subjects.devs[Dev_ID(s_id)])) &&
    (forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in toactivate_s_ids
            ==> OwnedTDs(k, s_id) * toactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * toactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * toactivate_do_ids == {}) &&
        // If a subject is not to be activated, then its objects must not to be
        // activated

    (true)
}

lemma Lemma_SubjObjActivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition(
    k:State, k':State, toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k') 

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, AllTDIDs(k'.objects), AllFDIDs(k'.objects), AllDOIDs(k'.objects))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

    ensures IsValidState_SubjsOwnObjsThenInSamePartition(k')
{
    forall s_id, o_id | s_id in AllSubjsIDs(k'.subjects) && DoOwnObj(k', s_id, o_id)
        ensures SubjPID(k', s_id) == ObjPID(k', o_id)
    {
        if(s_id !in toactivate_s_ids)
        {
            assert DoOwnObj(k, s_id, o_id);
            Lemma_SubjObjActivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition_Private(k, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, s_id, o_id);
            assert TD_ID(o_id) !in toactivate_td_ids;
            assert FD_ID(o_id) !in toactivate_fd_ids;
            assert DO_ID(o_id) !in toactivate_do_ids;

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
            assert s_id in toactivate_s_ids;

            assert SubjPID_SlimState(k'.subjects, s_id) == pid;
            if(Drv_ID(s_id) in k.subjects.drvs)
            {
                assert TD_ID(o_id) in toactivate_td_ids || 
                       FD_ID(o_id) in toactivate_fd_ids ||
                       DO_ID(o_id) in toactivate_do_ids;

                assert ObjPID(k', o_id) == pid;
            }
            else
            {
                assert Dev_ID(s_id) in k.subjects.devs;
                assert TD_ID(o_id) in toactivate_td_ids || 
                       FD_ID(o_id) in toactivate_fd_ids ||
                       DO_ID(o_id) in toactivate_do_ids;

                assert ObjPID(k', o_id) == pid;
            }
        }
    }
}

lemma Lemma_SubjObjActivate_NewK_UniqueIDsAndOwnedObjs(k:State, k':State)
    requires IsValidState(k)
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    ensures K_UniqueIDsAndOwnedObjs(k'.subjects, AllTDIDs(k'.objects), AllFDIDs(k'.objects), AllDOIDs(k'.objects))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjActivate_FulfillCommonPreConditionsOfKAndNewK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires pid != NULL
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)  

    ensures SubjObjActivate_PreConditionsOfK(k')
    ensures IsValidState_SubjsOwnObjsThenInSamePartition(k')
    ensures SubjObjActivate_CommonPreConditionsOfKAndNewK(
                k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids)
{
    Lemma_SubjObjActivate_NewK_UniqueIDsAndOwnedObjs(k ,k');
    Lemma_SubjObjActivate_NewK_SubjsObjsPIDsInNewK(k, k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
    Lemma_SubjObjActivate_NewK_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
    Lemma_SubjObjActivate_NewK_CertainTDsToActivateMustBeCleared(k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
    Lemma_SubjObjActivate_NewK_FulfillNextThreePredicates(k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
    Lemma_SubjObjActivate_NewK_FulfillNextPredicatesOfK(k, k_params);
    Lemma_SubjObjActivate_NewK_FulfillNextPredicatesOfNewK(k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
}

lemma Lemma_SubjObjActivate_FindReachableActiveTDsStatesFromActiveTDsState_ReturnsReachableTDsStates(
    k':State, k'_params:ReachableTDsKParams, k'_active_devs:set<Dev_ID>, k'_active_tds_state:TDs_Vals,
    explored_tds_states:seq<set<TDs_Vals>>, found_tds_states:set<TDs_Vals>
)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_PreConditionsOfK(k')
    
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

lemma Lemma_SubjObjActivate_NewK_FulfillSI2(
    k:State, k':State,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k.pids == k'.pids

    requires pid != NULL
    requires pid in k'.pids
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)

    ensures IsSecureState_SI2(k')
{
    assert AllSubjsIDs(k'.subjects) == AllSubjsIDs(k.subjects);
    assert AllObjsIDs(k'.objects) == AllObjsIDs(k.objects);

    forall s_id | s_id in AllSubjsIDs(k'.subjects) && SubjPID(k', s_id) != NULL
        ensures SubjPID(k', s_id) in k'.pids
    {
        assert s_id in toactivate_s_ids || SubjPID(k, s_id) != NULL;
        assert s_id in AllSubjsIDs(k.subjects);
    }

    forall o_id | o_id in AllObjsIDs(k'.objects) && ObjPID(k', o_id) != NULL
        ensures ObjPID(k', o_id) in k'.pids
    {
        // Dafny can automatically prove this lemma
    }
}

lemma Lemma_DrvDevActivate_SubjsNotBeingActivatedDoNotOwnAnyObjsBeingActivated(
    k:State, toactivate_s_ids:set<Subject_ID>,
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)

    requires toactivate_s_ids <= AllSubjsIDs(k.subjects)
    requires forall s_id :: s_id in toactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) == NULL
        // Requirement: All subjects to be activated are inactive in k 
    requires forall td_id :: td_id in toactivate_td_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in toactivate_fd_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in toactivate_do_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    ensures forall s_id :: s_id in toactivate_s_ids
            ==> s_id !in AllActiveSubjs_SlimState(k.subjects)
    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects) &&
                s_id !in toactivate_s_ids
            ==> OwnedTDs(k, s_id) * toactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * toactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * toactivate_do_ids == {}
{
    assert forall s_id :: s_id in toactivate_s_ids
            ==> s_id !in AllActiveSubjs_SlimState(k.subjects);

    assert forall o_id, s_id1, s_id2 :: 
        s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
        DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
        ==> s_id1 == s_id2;

    forall s_id | s_id in AllSubjsIDs(k.subjects) &&
                s_id !in toactivate_s_ids
        ensures OwnedTDs(k, s_id) * toactivate_td_ids == {}
        ensures OwnedFDs(k, s_id) * toactivate_fd_ids == {}
        ensures OwnedDOs(k, s_id) * toactivate_do_ids == {}
    { 
        if(exists td_id :: td_id in OwnedTDs(k, s_id) && td_id in toactivate_td_ids)
        {
            var td_id :| td_id in OwnedTDs(k, s_id) && td_id in toactivate_td_ids;
            var s_id2 :| s_id2 in toactivate_s_ids && td_id in OwnedTDs(k, s_id2);

            // Show conflict
            assert DoOwnObj(k, s_id, td_id.oid);
            assert DoOwnObj(k, s_id2, td_id.oid);
        }

        if(exists fd_id :: fd_id in OwnedFDs(k, s_id) && fd_id in toactivate_fd_ids)
        {
            var fd_id :| fd_id in OwnedFDs(k, s_id) && fd_id in toactivate_fd_ids;
            var s_id2 :| s_id2 in toactivate_s_ids && fd_id in OwnedFDs(k, s_id2);

            // Show conflict
            assert DoOwnObj(k, s_id, fd_id.oid);
            assert DoOwnObj(k, s_id2, fd_id.oid);
        }

        if(exists do_id :: do_id in OwnedDOs(k, s_id) && do_id in toactivate_do_ids)
        {
            var do_id :| do_id in OwnedDOs(k, s_id) && do_id in toactivate_do_ids;
            var s_id2 :| s_id2 in toactivate_s_ids && do_id in OwnedDOs(k, s_id2);

            // Show conflict
            assert DoOwnObj(k, s_id, do_id.oid);
            assert DoOwnObj(k, s_id2, do_id.oid);
        }
    }
}

lemma Lemma_DrvDevActivate_AllObjsToBeActivatedAreInactiveInK(
    k:State, toactivate_s_ids:set<Subject_ID>,
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)

    requires toactivate_s_ids <= AllSubjsIDs(k.subjects)
    requires forall s_id :: s_id in toactivate_s_ids
            ==> SubjPID_SlimState(k.subjects, s_id) == NULL
        // Requirement: All subjects to be activated are inactive in k 
    requires forall td_id :: td_id in toactivate_td_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in toactivate_fd_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in toactivate_do_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    ensures forall td_id :: td_id in toactivate_td_ids
            ==> ObjPID_KObjects(k.objects, td_id.oid) == NULL
    ensures forall fd_id :: fd_id in toactivate_fd_ids
            ==> ObjPID_KObjects(k.objects, fd_id.oid) == NULL
    ensures forall do_id :: do_id in toactivate_do_ids
            ==> ObjPID_KObjects(k.objects, do_id.oid) == NULL
{
    forall td_id | td_id in toactivate_td_ids
        ensures ObjPID_KObjects(k.objects, td_id.oid) == NULL
    {
        assert exists s_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, td_id.oid);
        assert ObjPID_KObjects(k.objects, td_id.oid) == NULL;
    }

    forall fd_id | fd_id in toactivate_fd_ids
        ensures ObjPID_KObjects(k.objects, fd_id.oid) == NULL
    {
        assert exists s_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, fd_id.oid);
        assert ObjPID_KObjects(k.objects, fd_id.oid) == NULL;
    }

    forall do_id | do_id in toactivate_do_ids
        ensures ObjPID_KObjects(k.objects, do_id.oid) == NULL
    {
        assert exists s_id :: s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, do_id.oid);
        assert ObjPID_KObjects(k.objects, do_id.oid) == NULL;
    }
}

predicate P_Lemma_DrvActivate_NoHCodedTDIsBeingActivated(k:State, toactivate_td_ids:set<TD_ID>)
{
    var hcoded_td_ids := AllHCodedTDIDs(k.subjects);
    var toactivate_hcoded_td_ids := set td_id | td_id in hcoded_td_ids && td_id in toactivate_td_ids :: td_id;

    toactivate_hcoded_td_ids == {}
}

lemma Lemma_DrvActivate_NoHCodedTDIsBeingActivated(k:State, toactive_drv_id:Drv_ID, toactivate_td_ids:set<TD_ID>)
    requires IsValidState(k) && IsSecureState(k)

    requires IsDrvID(k, toactive_drv_id)
    requires forall td_id :: td_id in toactivate_td_ids
                ==> td_id in OwnedTDs(k, toactive_drv_id.sid)

    ensures P_Lemma_DrvActivate_NoHCodedTDIsBeingActivated(k, toactivate_td_ids)
{
    assert (forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2);
    if(!P_Lemma_DrvActivate_NoHCodedTDIsBeingActivated(k, toactivate_td_ids))
    {
        var hcoded_td_ids := AllHCodedTDIDs(k.subjects);
        var toactivate_hcoded_td_ids := set td_id | td_id in hcoded_td_ids && td_id in toactivate_td_ids :: td_id;

        var td_id :| td_id in toactivate_hcoded_td_ids;

        assert td_id in toactivate_td_ids;
        assert td_id in hcoded_td_ids;

        assert td_id in OwnedTDs(k, toactive_drv_id.sid);
        assert DoOwnObj(k, toactive_drv_id.sid, td_id.oid);

        // Show conflict
        assert exists dev_id :: dev_id in k.subjects.devs &&
                      td_id == k.subjects.devs[dev_id].hcoded_td_id;
        var dev_id :| dev_id in k.subjects.devs &&
                      td_id == k.subjects.devs[dev_id].hcoded_td_id;
        assert DoOwnObj(k, dev_id.sid, td_id.oid);
        assert false;
    }
}

lemma Lemma_DrvDevActivate_HCodedTDsValsAreUnchanged(
    k:State, k'_subjects_devs:map<Dev_ID, Dev_State>, k'_objects:Objects, toactivate_td_ids:set<TD_ID>, pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid);

    requires MapGetKeys(k'_subjects_devs) == MapGetKeys(k.subjects.devs)
    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    
    ensures forall dev_id :: dev_id in k'_subjects_devs
                ==> k'_objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val == k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvActivate_ObjsIDsInDrvsAreUnchanged(k:State, k'_subjects:Subjects, drv_id:Drv_ID, old_drv_state:Drv_State, new_drv_state:Drv_State)
    requires drv_id in k.subjects.drvs

    requires old_drv_state == IDToDrv(k, drv_id)
    requires new_drv_state.td_ids == old_drv_state.td_ids
    requires new_drv_state.fd_ids == old_drv_state.fd_ids
    requires new_drv_state.do_ids == old_drv_state.do_ids
    requires k'_subjects.drvs == k.subjects.drvs[drv_id := new_drv_state]

    ensures forall drv_id :: drv_id in k'_subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires toactivate_s_ids <= AllSubjsIDs(k.subjects) 
    requires forall td_id :: td_id in toactivate_td_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in toactivate_fd_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in toactivate_do_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    requires K_UniqueIDsAndOwnedObjs(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

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
    Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs_OwnedObjsAreInNewK(k, k'_subjects, k'_objects, k'_params, 
        toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

    forall s_id, o_id | s_id in AllSubjsIDs(k'_params.subjects) &&
                    DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)
        ensures k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
    {
        if(s_id in toactivate_s_ids)
        {
            Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsBeingActivated(
                k, k'_subjects, k'_objects, k'_params, 
                toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid, s_id, o_id);
        }
        else
        {
            Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsNotBeingActivated(
                k, k'_subjects, k'_objects, k'_params, 
                toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid, s_id, o_id);
        }
    }
}

lemma Lemma_DrvActivate_SameActiveDevsInKAndNewK(
    k:State, k'_subjects:Subjects, drv_id:Drv_ID, old_drv_state:Drv_State, new_drv_state:Drv_State
)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k.subjects.drvs) && (Dev_ID(dev_sid) in k.subjects.devs)
         ==> (drv_sid != dev_sid)

    requires drv_id in k.subjects.drvs

    requires old_drv_state == IDToDrv(k, drv_id)
    requires new_drv_state.td_ids == old_drv_state.td_ids
    requires new_drv_state.fd_ids == old_drv_state.fd_ids
    requires new_drv_state.do_ids == old_drv_state.do_ids
    requires k'_subjects.drvs == k.subjects.drvs[drv_id := new_drv_state]
    requires k'_subjects.devs == k.subjects.devs

    ensures AllActiveDevs(k) == AllActiveDevs_SlimState(k'_subjects)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDevActivate_NonHCodedTDsAreClearedAsTC21(
    k:State, k'_hcoded_td_ids:set<TD_ID>, k'_objects:Objects, toactivate_td_ids:set<TD_ID>, pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k) 
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid)

    requires AllTDIDs(k'_objects) == AllTDIDs(k.objects)
    requires k'_hcoded_td_ids == AllHCodedTDIDs(k.subjects)

    ensures forall td_id :: td_id in AllTDIDs(k'_objects) &&
                    ObjPID_KObjects(k'_objects, td_id.oid) != ObjPID_KObjects(k.objects, td_id.oid) &&
                    ObjPID_KObjects(k'_objects, td_id.oid) != NULL &&
                        // For a transition from k to k', if a TD is activated (or moved) into a partition
                    td_id !in k'_hcoded_td_ids
                        // TD is not a hardcoded TD
                ==> IsTDClearVal(k'_objects.active_non_hcoded_tds, td_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDevExternalObjsActivate_FDsAreClearedAsTC22(
    k:State, k'_objects:Objects, toactivate_fd_ids:set<FD_ID>, pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k) 
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid)

    requires AllFDIDs(k'_objects) == AllFDIDs(k.objects)

    ensures forall fd_id :: fd_id in AllFDIDs(k'_objects) &&
                    ObjPID_KObjects(k'_objects, fd_id.oid) != ObjPID_KObjects(k.objects, fd_id.oid) &&
                    ObjPID_KObjects(k'_objects, fd_id.oid) != NULL
                        // For a transition from k to k', if a FD is activated (or moved) into a partition
                ==> IsFDClearVal(k'_objects.active_fds, fd_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DrvDevExternalObjsActivate_DOsAreClearedAsTC23(
    k:State, k'_objects:Objects, toactivate_do_ids:set<DO_ID>, pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k) 
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid)

    requires AllDOIDs(k'_objects) == AllDOIDs(k.objects)

    ensures forall do_id :: do_id in AllDOIDs(k'_objects) &&
                    ObjPID_KObjects(k'_objects, do_id.oid) != ObjPID_KObjects(k.objects, do_id.oid) &&
                    ObjPID_KObjects(k'_objects, do_id.oid) != NULL
                        // For a transition from k to k', if a DO is activated (or moved) into a partition
                ==> IsDOClearVal(k'_objects.active_dos, do_id)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_DevActivate_ObjsIDsInDevsAreUnchanged(k:State, k'_subjects:Subjects, dev_id:Dev_ID, old_dev_state:Dev_State, new_dev_state:Dev_State)
    requires dev_id in k.subjects.devs

    requires old_dev_state == IDToDev(k, dev_id)
    requires new_dev_state.hcoded_td_id == old_dev_state.hcoded_td_id
    requires new_dev_state.td_ids == old_dev_state.td_ids
    requires new_dev_state.fd_ids == old_dev_state.fd_ids
    requires new_dev_state.do_ids == old_dev_state.do_ids
    requires k'_subjects.devs == k.subjects.devs[dev_id := new_dev_state]

    ensures forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NewK_AllActiveDevsHaveNonNullPID(k'_subjects:Subjects)
    requires forall drv_sid, dev_sid :: 
         (Drv_ID(drv_sid) in k'_subjects.drvs) && (Dev_ID(dev_sid) in k'_subjects.devs)
         ==> (drv_sid != dev_sid)

    ensures forall dev_id2 :: dev_id2 in AllActiveDevs_SlimState(k'_subjects)
                ==> IsDevID_SlimState(k'_subjects, dev_id2) &&
                    SubjPID_DevID_SlimState(k'_subjects, dev_id2) != NULL
{
    forall dev_id2 | dev_id2 in AllActiveDevs_SlimState(k'_subjects)
        ensures IsDevID_SlimState(k'_subjects, dev_id2)
        ensures SubjPID_DevID_SlimState(k'_subjects, dev_id2) != NULL
    {
        assert IsDevID_SlimState(k'_subjects, dev_id2);
        assert SubjPID_SlimState(k'_subjects, dev_id2.sid) != NULL;
    }
}

lemma Lemma_NewK_HCodedTDsOfAllActiveDevsRefObjInDevs(
    k:State, k_params:ReachableTDsKParams,
    k'_params:ReachableTDsKParams, k'_subjects:Subjects, k'_active_devs:set<Dev_ID>
)
    requires IsValidState(k) && IsSecureState(k) 
    requires k_params == KToKParams(k) 

    requires AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)
    
    requires MapGetKeys(k'_params.subjects.drvs) == MapGetKeys(KToKParams(k).subjects.drvs)
    requires MapGetKeys(k'_params.subjects.devs) == MapGetKeys(KToKParams(k).subjects.devs)
    requires k'_params.objs_td_ids == KToKParams(k).objs_td_ids
    requires k'_params.hcoded_td_ids == KToKParams(k).hcoded_td_ids
    requires k'_params.hcoded_tds == KToKParams(k).hcoded_tds

    requires k'_params.subjects == k'_subjects

    requires forall dev_id :: dev_id in k'_active_devs
                ==> dev_id.sid in AllSubjsIDs(k'_subjects)
    requires forall dev_id :: dev_id in k'_active_devs
                ==> IsDevID_SlimState(k'_subjects, dev_id)

    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id) &&
                (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)

    ensures forall dev_id2 :: dev_id2 in k'_active_devs
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k'_params.subjects, dev_id2).td_ids <= k'_params.objs_td_ids
{
    Lemma_KParams_ValidAndSecureK_HCodedTDsOfDevRefObjInDev(k, k_params);
    assert forall dev_id2 :: IsDevID_SlimState(k_params.subjects, dev_id2)
                ==> DevHCodedTDRefsObjsInSameDev_SlimState(k_params.subjects, k_params.hcoded_tds, dev_id2) &&
                    IDToDev_SlimState(k_params.subjects, dev_id2).td_ids <= k_params.objs_td_ids;

    forall dev_id2 | dev_id2 in k'_active_devs
        ensures DevHCodedTDRefsObjsInSameDev_SlimState(k'_params.subjects, k'_params.hcoded_tds, dev_id2)
        ensures IDToDev_SlimState(k'_params.subjects, dev_id2).td_ids <= k'_params.objs_td_ids
    {
        assert IsDevID_SlimState(k_params.subjects, dev_id2);
    }
}

lemma Lemma_ExternalObjsActivate_AllObjsToBeActivatedAreExternalObjs(
    k:State,
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    (TD_ID(o_id) in toactivate_td_ids || FD_ID(o_id) in toactivate_fd_ids || DO_ID(o_id) in toactivate_do_ids)
                ==> !DoOwnObj(k, s_id, o_id)
        // Requirement: no subject owns these external objects

    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects)
            ==> OwnedTDs(k, s_id) * toactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * toactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * toactivate_do_ids == {}
{
    forall s_id | s_id in AllSubjsIDs(k.subjects)
        ensures OwnedTDs(k, s_id) * toactivate_td_ids == {}
        ensures OwnedFDs(k, s_id) * toactivate_fd_ids == {}
        ensures OwnedDOs(k, s_id) * toactivate_do_ids == {}
    {
        assert forall td_id :: td_id in toactivate_td_ids
                ==> !DoOwnObj(k, s_id, td_id.oid);
        assert forall fd_id :: fd_id in toactivate_fd_ids
                ==> !DoOwnObj(k, s_id, fd_id.oid);
        assert forall do_id :: do_id in toactivate_do_ids
                ==> !DoOwnObj(k, s_id, do_id.oid);

        assert forall td_id :: td_id in toactivate_td_ids
                ==> td_id !in OwnedTDs(k, s_id);
        assert forall fd_id :: fd_id in toactivate_fd_ids
                ==> fd_id !in OwnedFDs(k, s_id);
        assert forall do_id :: do_id in toactivate_do_ids
                ==> do_id !in OwnedDOs(k, s_id);
    }
}

lemma Lemma_SubjObjActivate_NewKParams_HasUnmodifiedVarsFromKParams(
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

    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires MapGetKeys(k.objects.hcoded_tds) == AllHCodedTDIDs(k.subjects)

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

lemma Lemma_ExternalObjsActivate_SubjsAndTheirObjsHaveSamePIDs(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams,
    tds_to_activate:set<TD_ID>, fds_to_activate:set<FD_ID>, dos_to_activate:set<DO_ID>
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
    requires tds_to_activate <= AllTDIDs(k.objects)
    requires fds_to_activate <= AllFDIDs(k.objects)
    requires dos_to_activate <= AllDOIDs(k.objects)
    requires forall s_id, td_id :: s_id in AllSubjsIDs(k.subjects) &&
                    td_id in tds_to_activate
                ==> !DoOwnObj(k, s_id, td_id.oid)
    requires forall s_id, fd_id :: s_id in AllSubjsIDs(k.subjects) &&
                    fd_id in fds_to_activate
                ==> !DoOwnObj(k, s_id, fd_id.oid)
    requires forall s_id, do_id :: s_id in AllSubjsIDs(k.subjects) &&
                    do_id in dos_to_activate
                ==> !DoOwnObj(k, s_id, do_id.oid)
        // Requirement: TDs/FDs/DOs to be activated must be external TDs/FDs/DOs
    requires forall td_id :: td_id in AllTDIDs(k.objects) && td_id !in tds_to_activate
                ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id)
    requires forall fd_id :: fd_id in AllFDIDs(k.objects) && fd_id !in fds_to_activate
                ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id)
    requires forall do_id :: do_id in AllDOIDs(k.objects) && do_id !in dos_to_activate
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
            assert td_id !in tds_to_activate;
            assert ObjStateUnchanged_TD(k.objects, k'_objects, td_id);
            assert k'_params.objs_pids[o_id] == ObjPID_KObjects(k.objects, td_id.oid);
        }
        else if(FD_ID(o_id) in AllFDIDs(k.objects))
        {
            var fd_id := FD_ID(o_id);
            assert fd_id !in fds_to_activate;
            assert ObjStateUnchanged_FD(k.objects, k'_objects, fd_id);
            assert k'_params.objs_pids[o_id] == ObjPID_KObjects(k.objects, fd_id.oid);
        }
        else
        {
            var do_id := DO_ID(o_id);
            assert DO_ID(o_id) in AllDOIDs(k.objects);
            assert do_id !in dos_to_activate;
            assert ObjStateUnchanged_DO(k.objects, k'_objects, do_id);
            assert k'_params.objs_pids[o_id] == ObjPID_KObjects(k.objects, do_id.oid);
        }
    }
}

lemma Lemma_ExternalObjsActivate_FulfillTC21(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams,
    tds_to_activate:set<TD_ID>, fds_to_activate:set<FD_ID>, dos_to_activate:set<DO_ID>,
    pid:Partition_ID
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

    requires MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires MapGetKeys(k.objects.hcoded_tds) == AllHCodedTDIDs(k.subjects)

    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in AllTDIDs(k.objects)
        // Requirement: Hardcoded TDs are in the TDs of the state
    requires tds_to_activate <= AllTDIDs(k.objects)
    requires fds_to_activate <= AllFDIDs(k.objects)
    requires dos_to_activate <= AllDOIDs(k.objects)
    requires forall s_id, td_id :: s_id in AllSubjsIDs(k.subjects) &&
                    td_id in tds_to_activate
                ==> !DoOwnObj(k, s_id, td_id.oid)
    requires forall s_id, fd_id :: s_id in AllSubjsIDs(k.subjects) &&
                    fd_id in fds_to_activate
                ==> !DoOwnObj(k, s_id, fd_id.oid)
    requires forall s_id, do_id :: s_id in AllSubjsIDs(k.subjects) &&
                    do_id in dos_to_activate
                ==> !DoOwnObj(k, s_id, do_id.oid)
        // Requirement: TDs/FDs/DOs to be activated must be external TDs/FDs/DOs
    requires forall td_id :: td_id in AllTDIDs(k.objects) && td_id !in tds_to_activate
                ==> ObjStateUnchanged_TD(k.objects, k'_objects, td_id)
    requires forall fd_id :: fd_id in AllFDIDs(k.objects) && fd_id !in fds_to_activate
                ==> ObjStateUnchanged_FD(k.objects, k'_objects, fd_id)
    requires forall do_id :: do_id in AllDOIDs(k.objects) && do_id !in dos_to_activate
                ==> ObjStateUnchanged_DO(k.objects, k'_objects, do_id)
        // Requirement: Other TDs/FDs/DOs are not modified

    requires pid != NULL
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, tds_to_activate, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, fds_to_activate, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, dos_to_activate, pid)

    ensures forall td_id :: td_id in AllTDIDs(k'_objects) &&
                    ObjPID_KObjects(k'_objects, td_id.oid) != ObjPID_KObjects(k.objects, td_id.oid) &&
                    ObjPID_KObjects(k'_objects, td_id.oid) != NULL &&
                        // For a transition from k to k', if a TD is activated (or moved) into a partition
                    td_id !in AllHCodedTDIDs(k'_subjects)
                        // TD is not a hardcoded TD
                ==> IsTDClearVal(k'_objects.active_non_hcoded_tds, td_id)
{
    forall td_id | td_id in AllTDIDs(k'_objects) &&
                    ObjPID_KObjects(k'_objects, td_id.oid) != ObjPID_KObjects(k.objects, td_id.oid) &&
                    ObjPID_KObjects(k'_objects, td_id.oid) != NULL &&
                        // For a transition from k to k', if a TD is activated (or moved) into a partition
                    td_id !in AllHCodedTDIDs(k'_subjects)
                        // TD is not a hardcoded TD
        ensures IsTDClearVal(k'_objects.active_non_hcoded_tds, td_id)
    {
        // Dafny can automatically prove this lemma
    }
}

lemma Lemma_DrvActivate_ProveSubjsObjsFulfillProperties(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    drv_id:Drv_ID, pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs

    requires drv_id in k.subjects.drvs
    requires pid != NULL
    requires SubjPID_SlimState(k.subjects, drv_id.sid) == NULL

    requires (forall id :: id in k.subjects.drvs[drv_id].td_ids ==> id in k.objects.inactive_non_hcoded_tds) &&
            (forall id :: id in k.subjects.drvs[drv_id].fd_ids ==> id in k.objects.inactive_fds) &&
            (forall id :: id in k.subjects.drvs[drv_id].do_ids ==> id in k.objects.inactive_dos)

    requires var drv_state := IDToDrv(k, drv_id);
             var new_drv_state := Drv_State(pid, drv_state.td_ids, drv_state.fd_ids, drv_state.do_ids);
             var new_drvs := k.subjects.drvs[drv_id := new_drv_state];
             k'_subjects == Subjects(new_drvs, k.subjects.devs)

    requires var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[drv_id].td_ids;
            var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[drv_id].fd_ids;
            var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[drv_id].do_ids;
            var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, tds_owned_by_drv, pid);
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_drv, pid);
            k'_objects == SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_drv, pid);

    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k'_objects)

    ensures SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, k.subjects.drvs[drv_id].td_ids, pid)
    ensures SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, k.subjects.drvs[drv_id].fd_ids, pid)
    ensures SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, k.subjects.drvs[drv_id].do_ids, pid)
    ensures SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, {drv_id.sid}, k.subjects.drvs[drv_id].td_ids, k.subjects.drvs[drv_id].fd_ids, k.subjects.drvs[drv_id].do_ids, pid)
{
    var tds_owned_by_drv:set<TD_ID> := k.subjects.drvs[drv_id].td_ids;
    var fds_owned_by_drv:set<FD_ID> := k.subjects.drvs[drv_id].fd_ids;
    var dos_owned_by_drv:set<DO_ID> := k.subjects.drvs[drv_id].do_ids;
    var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, tds_owned_by_drv, pid);
    var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_drv, pid);
    var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_drv, pid);

    assert k'_objects == t_objs3;
    assert AllTDIDs(t_objs3) == AllTDIDs(k.objects);
    assert AllTDIDs(k'_objects) == AllTDIDs(t_objs3);
    assert AllFDIDs(t_objs3) == AllFDIDs(k.objects);
    assert AllFDIDs(k'_objects) == AllFDIDs(t_objs3);
    assert AllDOIDs(t_objs3) == AllDOIDs(k.objects);
    assert AllDOIDs(k'_objects) == AllDOIDs(t_objs3);

    var toactivate_s_ids:set<Subject_ID> := {drv_id.sid};
    var toactivate_td_ids := tds_owned_by_drv;
    var toactivate_fd_ids := fds_owned_by_drv;
    var toactivate_do_ids := dos_owned_by_drv;

    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    forall td_id | td_id in toactivate_td_ids
        ensures ObjPID_KObjects(k.objects, td_id.oid) == NULL
    {
        assert DoOwnObj(k, drv_id.sid, td_id.oid);
        assert IsValidState_SubjsOwnObjsThenInSamePartition(k);
        assert SubjPID_SlimState(k.subjects, drv_id.sid) == NULL;
    }

    forall fd_id | fd_id in toactivate_fd_ids
        ensures fd_id in k.objects.inactive_fds
    {
        assert fd_id in AllFDIDs(k.objects);
        assert ObjPID_KObjects(k.objects, fd_id.oid) == NULL;
        reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    }
    assert SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid);

    forall do_id | do_id in toactivate_do_ids
        ensures do_id in k.objects.inactive_dos
    {
        assert do_id in AllDOIDs(k.objects);
        assert ObjPID_KObjects(k.objects, do_id.oid) == NULL;
        reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    }

    forall do_id | do_id in toactivate_do_ids
        ensures do_id in k'_objects.active_dos
        ensures k'_objects.active_dos[do_id].pid == pid
    {
        assert ObjPID_KObjects(k'_objects, do_id.oid) == pid;
        reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    }
    assert SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid);

    Lemma_DrvDevActivate_SubjsNotBeingActivatedDoNotOwnAnyObjsBeingActivated(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
    assert SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
}

lemma Lemma_DevActivate_ProveSubjsObjsFulfillProperties(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    dev_id:Dev_ID, pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs

    requires dev_id in k.subjects.devs
    requires pid != NULL
    requires SubjPID_SlimState(k.subjects, dev_id.sid) == NULL

    requires (forall id :: id in k.subjects.devs[dev_id].td_ids && id != k.subjects.devs[dev_id].hcoded_td_id
                         ==> id in k.objects.inactive_non_hcoded_tds) &&
            (forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.inactive_fds) &&
            (forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.inactive_dos)

    requires var dev_state := IDToDev(k, dev_id);
             var new_dev_state := Dev_State(pid, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
             var new_devs := k.subjects.devs[dev_id := new_dev_state];
             k'_subjects == Subjects(k.subjects.drvs, new_devs)

    requires var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
            var toactive_hcoded_td_id := IDToDev(k, dev_id).hcoded_td_id;
            var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};
            var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, toclear_td_ids, pid);
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_dev, pid);
            var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_dev, pid);
            k'_objects == SetHCodedTDsPIDs(t_objs3, {toactive_hcoded_td_id}, pid)

    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k'_objects)

    ensures SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, k.subjects.devs[dev_id].td_ids, pid)
    ensures SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, k.subjects.devs[dev_id].fd_ids, pid)
    ensures SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, k.subjects.devs[dev_id].do_ids, pid)
    ensures SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, {dev_id.sid}, k.subjects.devs[dev_id].td_ids, k.subjects.devs[dev_id].fd_ids, k.subjects.devs[dev_id].do_ids, pid)
{
    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    var toactive_hcoded_td_id := IDToDev(k, dev_id).hcoded_td_id;
    var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};
    var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, toclear_td_ids, pid);
    var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_dev, pid);
    var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_dev, pid);
    var t_objs4 := SetHCodedTDsPIDs(t_objs3, {toactive_hcoded_td_id}, pid);

    assert k'_objects == t_objs4;
    assert AllTDIDs(t_objs3) == AllTDIDs(k.objects);
    assert AllTDIDs(k'_objects) == AllTDIDs(t_objs3);
    assert AllFDIDs(t_objs3) == AllFDIDs(k.objects);
    assert AllFDIDs(k'_objects) == AllFDIDs(t_objs3);
    assert AllDOIDs(t_objs3) == AllDOIDs(k.objects);
    assert AllDOIDs(k'_objects) == AllDOIDs(t_objs3);

    var toactivate_s_ids:set<Subject_ID> := {dev_id.sid};
    var toactivate_td_ids := tds_owned_by_dev;
    var toactivate_fd_ids := fds_owned_by_dev;
    var toactivate_do_ids := dos_owned_by_dev;

    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    forall td_id | td_id in toactivate_td_ids
        ensures ObjPID_KObjects(k.objects, td_id.oid) == NULL
    {
        assert DoOwnObj(k, dev_id.sid, td_id.oid);
        assert IsValidState_SubjsOwnObjsThenInSamePartition(k);
        assert SubjPID_SlimState(k.subjects, dev_id.sid) == NULL;
    }

    forall fd_id | fd_id in toactivate_fd_ids
        ensures fd_id in k.objects.inactive_fds
    {
        assert fd_id in AllFDIDs(k.objects);
        assert ObjPID_KObjects(k.objects, fd_id.oid) == NULL;
        reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    }
    assert SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid);

    forall do_id | do_id in toactivate_do_ids
        ensures do_id in k.objects.inactive_dos
    {
        assert do_id in AllDOIDs(k.objects);
        assert ObjPID_KObjects(k.objects, do_id.oid) == NULL;
        reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    }

    forall do_id | do_id in toactivate_do_ids
        ensures do_id in k'_objects.active_dos
        ensures k'_objects.active_dos[do_id].pid == pid
    {
        assert ObjPID_KObjects(k'_objects, do_id.oid) == pid;
        reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    }
    assert SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid);

    Lemma_DrvDevActivate_SubjsNotBeingActivatedDoNotOwnAnyObjsBeingActivated(k, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
    assert SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);
}

lemma Lemma_DevActivate_ProveSubjObjActivate_UnchangedStateVarsBetweenKandNewK(
    k:State, dev_id:Dev_ID, pid:Partition_ID, k':State
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)

    requires dev_id in k.subjects.devs
    requires (forall id :: id in k.subjects.devs[dev_id].td_ids && id != k.subjects.devs[dev_id].hcoded_td_id ==> id in k.objects.inactive_non_hcoded_tds) &&
            (forall id :: id in k.subjects.devs[dev_id].fd_ids ==> id in k.objects.inactive_fds) &&
            (forall id :: id in k.subjects.devs[dev_id].do_ids ==> id in k.objects.inactive_dos)
    requires pid != NULL

    requires var dev_state := IDToDev(k, dev_id);
             var new_dev_state := Dev_State(pid, dev_state.hcoded_td_id, dev_state.td_ids, dev_state.fd_ids, dev_state.do_ids);
             var new_devs := k.subjects.devs[dev_id := new_dev_state];
             k'.subjects == Subjects(k.subjects.drvs, new_devs)

    requires var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
            var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
            var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
            var toactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
            var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};
            var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, toclear_td_ids, pid);
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_dev, pid);
            var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_dev, pid);
            toactive_hcoded_td_id in t_objs3.hcoded_tds &&
            k'.objects == SetHCodedTDsPIDs(t_objs3, {toactive_hcoded_td_id}, pid)

    requires k'.pids == k.pids
    requires k'.tds_to_all_states == k.tds_to_all_states

    ensures SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
{
    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();

    var tds_owned_by_dev:set<TD_ID> := k.subjects.devs[dev_id].td_ids;
    var fds_owned_by_dev:set<FD_ID> := k.subjects.devs[dev_id].fd_ids;
    var dos_owned_by_dev:set<DO_ID> := k.subjects.devs[dev_id].do_ids;
    var toactive_hcoded_td_id := k.subjects.devs[dev_id].hcoded_td_id;
    var toclear_td_ids := tds_owned_by_dev - {toactive_hcoded_td_id};
    var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, toclear_td_ids, pid);
    var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fds_owned_by_dev, pid);
    var t_objs3 := SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, dos_owned_by_dev, pid);

    // Prove toactive_hcoded_td_id in t_objs3.hcoded_tds
    assert toactive_hcoded_td_id in k.objects.hcoded_tds;
    assert toactive_hcoded_td_id in t_objs3.hcoded_tds;

    var new_objects := SetHCodedTDsPIDs(t_objs3, {toactive_hcoded_td_id}, pid);

    assert forall id :: id in new_objects.active_non_hcoded_tds
        ==> new_objects.active_non_hcoded_tds[id].pid != NULL;
}

lemma Lemma_ExternalObjsActivate_ProveSubjsObjsFulfillProperties(
    k:State, k'_subjects:Subjects, k'_objects:Objects,
    td_ids:set<TD_ID>, fd_ids:set<FD_ID>, do_ids:set<DO_ID>, pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs

    requires k'_subjects == k.subjects

    requires td_ids <= AllTDIDs(k.objects)
    requires fd_ids <= AllFDIDs(k.objects)
    requires do_ids <= AllDOIDs(k.objects)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    o_id in (TDIDsToObjIDs(td_ids) + FDIDsToObjIDs(fd_ids) + DOIDsToObjIDs(do_ids))
                ==> !DoOwnObj(k, s_id, o_id)

    requires pid != NULL

    requires (forall id :: id in td_ids ==> id in k.objects.inactive_non_hcoded_tds) &&
            (forall id :: id in fd_ids ==> id in k.objects.inactive_fds) &&
            (forall id :: id in do_ids ==> id in k.objects.inactive_dos)
    requires var t_objs1 := SetPIDsAndClear_InactiveNonHCodedTDs_ToNonNULLPID(k.objects, td_ids, pid);
            var t_objs2 := SetPIDsAndClear_InactiveFDs_ToNonNULLPID(t_objs1, fd_ids, pid);
            k'_objects == SetPIDsAndClear_InactiveDOs_ToNonNULLPID(t_objs2, do_ids, pid)

    requires IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k'_objects)

    ensures SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, td_ids, pid)
    ensures SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, fd_ids, pid)
    ensures SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, do_ids, pid)
    ensures SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, {}, td_ids, fd_ids, do_ids, pid)
{
    var tds_owned_by_drv:set<TD_ID> := td_ids;
    var fds_owned_by_drv:set<FD_ID> := fd_ids;
    var dos_owned_by_drv:set<DO_ID> := do_ids;

    var toactivate_s_ids:set<Subject_ID> := {};
    var toactivate_td_ids := tds_owned_by_drv;
    var toactivate_fd_ids := fds_owned_by_drv;
    var toactivate_do_ids := dos_owned_by_drv;

    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    forall fd_id | fd_id in toactivate_fd_ids
        ensures fd_id in k.objects.inactive_fds
    {
        assert fd_id in AllFDIDs(k.objects);
        assert ObjPID_KObjects(k.objects, fd_id.oid) == NULL;
        reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    }
    assert SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, fd_ids, pid);

    forall do_id | do_id in toactivate_do_ids
        ensures do_id in k.objects.inactive_dos
    {
        assert do_id in AllDOIDs(k.objects);
        assert ObjPID_KObjects(k.objects, do_id.oid) == NULL;
        reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    }

    forall do_id | do_id in toactivate_do_ids
        ensures do_id in k'_objects.active_dos
        ensures k'_objects.active_dos[do_id].pid == pid
    {
        assert ObjPID_KObjects(k'_objects, do_id.oid) == pid;
        reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    }
    assert SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, do_ids, pid);

    Lemma_ExternalObjsActivate_AllObjsToBeDeactivatedAreExternalObjs(k, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids);
    assert SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, {}, td_ids, fd_ids, do_ids, pid);
}




//******** Private Lemmas  ********//
lemma Lemma_SubjObjActivate_NewK_SubjsObjsPIDsInNewK(
    k:State, k':State, toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k') 

    requires K_UniqueIDsAndOwnedObjs(k'.subjects, AllTDIDs(k'.objects), AllFDIDs(k'.objects), AllDOIDs(k'.objects))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

    ensures IsValidState_SubjsOwnObjsThenInSamePartition(k')
    ensures SubjObjActivate_SubjsObjsPIDsInNewK(k')
{
    Lemma_SubjObjActivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition(k, k', toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid);

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

lemma Lemma_SubjObjActivate_NewK_PreConditionsOfSubjObjToActivate(
    k:State, k':State, toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState_Subjects(k)
    requires IsValidState_Objects(k)
    requires IsValidState_SubjsOwnObjsThenInSamePartition(k)
    
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k') 

    requires pid != NULL
    requires K_UniqueIDsAndOwnedObjs(k'.subjects, AllTDIDs(k'.objects), AllFDIDs(k'.objects), AllDOIDs(k'.objects))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

    ensures SubjObjActivate_PreConditionsOfK(k)
    ensures SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)
{
    Lemma_AllActiveObjs_SlimState_Property(k.objects);

    forall drv_id2:Drv_ID | IsDrvID(k, drv_id2) &&
                    drv_id2.sid !in toactivate_s_ids
        ensures k'.subjects.drvs[drv_id2] == k.subjects.drvs[drv_id2]
    {
        assert drv_id2.sid in AllSubjsIDs(k.subjects);
        assert drv_id2 in k.subjects.drvs;
    }

    // Prove AllActiveTDs(k') == AllActiveTDs(k) + toactivate_td_ids
    Lemma_SubjObjActivate_NewK_PreConditionsOfSubjObjToActivate_ProveRelationshipOfActiveTDs(k, k', toactivate_td_ids, pid);
    assert AllActiveTDs(k') == AllActiveTDs(k) + toactivate_td_ids;

    // Prove AllActiveTDs(k) * toactivate_td_ids == {}
    forall td_id | td_id in AllActiveTDs(k)
        ensures td_id !in toactivate_td_ids
    {
        assert IsValidState_Objects_UniqueObjIDs(k.objects);
        reveal IsValidState_Objects_UniqueObjIDs();
        assert ObjPID(k, td_id.oid) != NULL;

        if(td_id in toactivate_td_ids)
        {
            assert ObjPID_KObjects(k.objects, td_id.oid) == NULL;
            assert ObjPID(k, td_id.oid) == NULL;
            assert false;
        }
    }
    Lemma_SetsWithoutSameElemHaveEmptyIntersection(AllActiveTDs(k), toactivate_td_ids);
    assert AllActiveTDs(k) * toactivate_td_ids == {};
}

lemma Lemma_SubjObjActivate_NewK_PreConditionsOfSubjObjToActivate_ProveRelationshipOfActiveTDs(
    k:State, k':State, toactivate_td_ids:set<TD_ID>, pid:Partition_ID
)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires MapGetKeys(k'.objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)
    requires MapGetKeys(k.objects.hcoded_tds) == AllHCodedTDIDs(k.subjects)
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires pid != NULL

    ensures AllActiveTDs(k') == AllActiveTDs(k) + toactivate_td_ids
{
    assert forall td_id :: td_id in AllTDIDs(k.objects) &&
                td_id !in toactivate_td_ids
            ==> ObjStateUnchanged_TD(k.objects, k'.objects, td_id);

    assert forall id :: id in AllActiveTDs(k') ==> id in AllActiveTDs(k) + toactivate_td_ids;
    forall td_id |  td_id in AllActiveTDs(k) + toactivate_td_ids
        ensures td_id in AllActiveTDs(k')
    {
        if(td_id in AllActiveTDs(k))
        {
            assert td_id in AllActiveTDs(k');
        }

        if(td_id in toactivate_td_ids)
        {
            assert td_id in AllActiveTDs(k');
        }
    }
}

// (needs 40s to verify)
lemma Lemma_SubjObjActivate_NewK_CertainTDsToActivateMustBeCleared(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')

    requires pid != NULL
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)  

    ensures SubjObjActivate_CertainTDsToActivateMustBeCleared(k, k', toactivate_s_ids)
{
    Lemma_KToKParams_Properties(k', k'_params);
    assert k'_params.subjects == k'.subjects;

    Lemma_NewKParams_SameSubjIDsOwnershipInSuccessiveStates(k, k'.subjects, k_params, k'_params);

    forall dev_id2:Dev_ID, td_id2 | IsDevID(k, dev_id2) && 
                    dev_id2.sid in toactivate_s_ids &&
                    td_id2 in TDsRefedByDevHCodedTDWithR(BuildMap_DevsToHCodedTDVals(k'.subjects, k'.objects), dev_id2)
        ensures td_id2 in k'.objects.active_non_hcoded_tds
        ensures IsTDClearVal(k'.objects.active_non_hcoded_tds, td_id2)
    {
        assert DoOwnObj(k, dev_id2.sid, td_id2.oid);
    }
}

lemma Lemma_SubjObjActivate_NewK_FulfillNextThreePredicates(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')
    requires SubjObjActivate_SubjsObjsPIDsInNewK(k')
    requires SubjObjActivate_PreConditionsOfSubjObjToActivate(k, k', toactivate_s_ids, toactivate_td_ids)

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires pid != NULL
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)  

    ensures SubjObjActivate_ReachableActiveTDsStatesInK_Fulfill51And3And5And6(k)
    ensures CanActiveDevReadActiveTD_KParams_PreConditions(k_params)
    ensures SubjObjActivate_PreConditionsOfK(k')
{
    Lemma_CanActiveDevReadActiveTD_SubjObjActivate_IfSubjsToActivateCanReadTDThenOwnTD_PreConditions(
        k, k_params, k', k'_params, toactivate_s_ids, toactivate_td_ids);
}

lemma Lemma_SubjObjActivate_NewK_FulfillNextPredicatesOfK(
    k:State, k_params:ReachableTDsKParams
)
    requires IsValidState(k) && IsSecureState(k)
    requires k_params == KToKParams(k)

    ensures forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
                ==> s_id1 == s_id2
        // Requirement: In k, no two subjects own the same object
    ensures forall dev_id2 :: dev_id2 in k.subjects.devs
                ==> DevHCodedTDRefsObjsInSameDev(k, dev_id2) &&
                    IDToDev(k, dev_id2).td_ids <= AllTDIDs(k.objects)
    ensures forall dev_id2, td_id2 :: IsDevID(k, dev_id2) &&
                    td_id2 in GetTransfersToTDsInHCodedTD(KToKParams(k).hcoded_tds, dev_id2)
                ==> td_id2 != k.subjects.devs[dev_id2].hcoded_td_id

    ensures forall dev_id :: dev_id in k.subjects.devs
                ==> (forall td_id :: td_id in k.objects.hcoded_tds[k.subjects.devs[dev_id].hcoded_td_id].val.trans_params_tds
                        ==> td_id !in k_params.hcoded_td_ids)
{
    forall dev_id2, td_id2 | IsDevID(k, dev_id2) &&
                    td_id2 in GetTransfersToTDsInHCodedTD(k_params.hcoded_tds, dev_id2)
        ensures td_id2 != k.subjects.devs[dev_id2].hcoded_td_id
    {
        assert td_id2 in HCodedTDValOfDev(k_params.hcoded_tds, dev_id2).trans_params_tds;
        assert td_id2 !in AllHCodedTDIDs(k.subjects);
    }
}

lemma Lemma_SubjObjActivate_NewK_FulfillNextPredicatesOfNewK(
    k:State, k_params:ReachableTDsKParams, k':State, k'_params:ReachableTDsKParams,
    toactivate_s_ids:set<Subject_ID>, toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'.objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK(k, k')

    requires k_params == KToKParams(k)
    requires k'_params == KToKParams(k')
    requires k'_params.hcoded_td_ids == k_params.hcoded_td_ids
    requires k'_params.hcoded_tds == k_params.hcoded_tds

    requires pid != NULL
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'.objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'.objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'.objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'.subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)  

    ensures forall dev_id:Dev_ID :: dev_id.sid in toactivate_s_ids && dev_id in k.subjects.devs
                ==> (dev_id in k'.subjects.devs &&
                    (forall td_id :: td_id in GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)
                        ==> GetTransfersToTDsInHCodedTD(k'_params.hcoded_tds, dev_id)[td_id].amodes != {R,W}))
        // Requirement: Activating devices do not have hardcoded R and W to the 
        // same object
    ensures forall td_id:TD_ID, dev_id:Dev_ID :: dev_id in k.subjects.devs &&
                dev_id.sid in toactivate_s_ids && 
                td_id in TDsRefedByDevHCodedTDWithR(k'_params.hcoded_tds, dev_id)
            ==> td_id in k'.objects.active_non_hcoded_tds &&
                k'.objects.active_non_hcoded_tds[td_id].val == TD_Val(map[], map[], map[])
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubjObjActivate_NewK_FulfillIsValidState_SubjsOwnObjsThenInSamePartition_Private(
    k:State,
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k)

    requires toactivate_td_ids <= AllTDIDs(k.objects)
    requires toactivate_fd_ids <= AllFDIDs(k.objects)
    requires toactivate_do_ids <= AllDOIDs(k.objects)

    requires s_id in AllSubjsIDs(k.subjects)

    requires OwnedTDs(k, s_id) * toactivate_td_ids == {}
    requires OwnedFDs(k, s_id) * toactivate_fd_ids == {}
    requires OwnedDOs(k, s_id) * toactivate_do_ids == {}

    requires DoOwnObj(k, s_id, o_id)

    ensures TD_ID(o_id) !in toactivate_td_ids
    ensures FD_ID(o_id) !in toactivate_fd_ids
    ensures DO_ID(o_id) !in toactivate_do_ids 
{
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(OwnedTDs(k, s_id), toactivate_td_ids);
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(OwnedFDs(k, s_id), toactivate_fd_ids);
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(OwnedDOs(k, s_id), toactivate_do_ids);
}

lemma Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs_OwnedObjsAreInNewK(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires K_UniqueIDsAndOwnedObjs(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

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

lemma Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsBeingActivated(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID, s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires K_UniqueIDsAndOwnedObjs(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects))
    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid) 

    requires IsSubjID(k.subjects, s_id)
    requires s_id in toactivate_s_ids
        // Requirement: The subject (<s_id>) is not being activated

    requires k'_params == ReachableTDsKParams(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects))
    requires DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)

    requires o_id in k'_params.objs_pids

    ensures k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id)
{
    assert TD_ID(o_id) in toactivate_td_ids || FD_ID(o_id) in toactivate_fd_ids || DO_ID(o_id) in toactivate_do_ids;
    assert k'_params.objs_pids[o_id] == SubjPID_SlimState(k'_params.subjects, s_id);
}

lemma Lemma_DrvDevActivate_NewK_SubjsAndTheirObjsHaveSamePIDs_SubjIsNotBeingActivated(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    pid:Partition_ID, s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires toactivate_s_ids <= AllSubjsIDs(k.subjects) 
    requires forall td_id :: td_id in toactivate_td_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in toactivate_fd_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in toactivate_do_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    requires SubjObjActivate_PropertiesOfNewTDs(k, k'_objects, toactivate_td_ids, pid)
    requires SubjObjActivate_PropertiesOfNewFDs(k, k'_objects, toactivate_fd_ids, pid)
    requires SubjObjActivate_PropertiesOfNewDOs(k, k'_objects, toactivate_do_ids, pid)
    requires SubjObjActivate_PropertiesOfNewSubjs(k, k'_subjects, toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, pid)

    requires IsSubjID(k.subjects, s_id)
    requires s_id !in toactivate_s_ids
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
    Lemma_DrvDevActivate_InSubjsNotBeingActivated_ObjsAreUnchanged(k, k'_subjects, k'_objects, k'_params, 
        toactivate_s_ids, toactivate_td_ids, toactivate_fd_ids, toactivate_do_ids, s_id, o_id);
    assert TD_ID(o_id) !in toactivate_td_ids && FD_ID(o_id) !in toactivate_fd_ids && DO_ID(o_id) !in toactivate_do_ids;

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

predicate SubjObjActivate_UnchangedStateVarsBetweenKandNewK_SlimState(k:State, k'_subjects:Subjects, k'_objects:Objects)
{
    (MapGetKeys(k'_subjects.drvs) == MapGetKeys(k.subjects.drvs)) &&
    (MapGetKeys(k'_subjects.devs) == MapGetKeys(k.subjects.devs)) &&
    (AllTDIDs(k'_objects) == AllTDIDs(k.objects)) &&
    (AllFDIDs(k'_objects) == AllFDIDs(k.objects)) &&
    (AllDOIDs(k'_objects) == AllDOIDs(k.objects)) &&
    (MapGetKeys(k'_objects.hcoded_tds) == MapGetKeys(k.objects.hcoded_tds)) &&
    (forall drv_id :: drv_id in k.subjects.drvs
                ==> (k'_subjects.drvs[drv_id].td_ids == k.subjects.drvs[drv_id].td_ids) &&
                    (k'_subjects.drvs[drv_id].fd_ids == k.subjects.drvs[drv_id].fd_ids) &&
                    (k'_subjects.drvs[drv_id].do_ids == k.subjects.drvs[drv_id].do_ids)) &&
    (forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].td_ids == k.subjects.devs[dev_id].td_ids) &&
                    (k'_subjects.devs[dev_id].fd_ids == k.subjects.devs[dev_id].fd_ids) &&
                    (k'_subjects.devs[dev_id].do_ids == k.subjects.devs[dev_id].do_ids)) &&
    (forall dev_id :: dev_id in k.subjects.devs
                ==> (k'_subjects.devs[dev_id].hcoded_td_id == k.subjects.devs[dev_id].hcoded_td_id)) &&

    (AllSubjsIDs(k'_subjects) == AllSubjsIDs(k.subjects)) &&
    (AllObjsIDs(k'_objects) == AllObjsIDs(k.objects)) &&

    (true)
}

lemma Lemma_DrvDevActivate_InSubjsNotBeingActivated_ObjsAreUnchanged(
    k:State, k'_subjects:Subjects, k'_objects:Objects, k'_params:ReachableTDsKParams, 
    toactivate_s_ids:set<Subject_ID>, 
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>,
    s_id:Subject_ID, o_id:Object_ID
)
    requires IsValidState(k)
    requires IsValidState_Objects_UniqueObjIDs(k'_objects)
        // Requirement: Objects have different internal IDs
    requires SubjObjActivate_UnchangedStateVarsBetweenKandNewK_SlimState(k, k'_subjects, k'_objects)

    requires toactivate_s_ids <= AllSubjsIDs(k.subjects) 
    requires forall td_id :: td_id in toactivate_td_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && td_id in OwnedTDs(k, s_id))
    requires forall fd_id :: fd_id in toactivate_fd_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && fd_id in OwnedFDs(k, s_id))
    requires forall do_id :: do_id in toactivate_do_ids
            ==> (exists s_id :: s_id in toactivate_s_ids && do_id in OwnedDOs(k, s_id))
        // Requirement: objects to be activated are owned by subjects to be activated

    requires IsSubjID(k.subjects, s_id)
    requires s_id !in toactivate_s_ids
        // Requirement: The subject (<s_id>) is not being activated
    
    requires forall dev_id :: dev_id in k'_subjects.devs
                ==> k'_subjects.devs[dev_id].hcoded_td_id in k'_subjects.devs[dev_id].td_ids
    requires forall dev_id, td_id :: 
                dev_id in k'_subjects.devs && td_id in k'_subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k'_objects)
        // Requirements can be proved with requirements above, but not recongized by Dafny
    requires k'_params == ReachableTDsKParams(k'_subjects, AllTDIDs(k'_objects), AllFDIDs(k'_objects), AllDOIDs(k'_objects),
                        AllHCodedTDIDs(k'_subjects), BuildMap_DevsToHCodedTDVals(k'_subjects, k'_objects), 
                        BuildMap_ObjIDsToPIDs(k'_objects), AllActiveTDs_SlimState(k'_objects))
    requires DoOwnObj_SlimState(k'_params.subjects, s_id, o_id)

    ensures TD_ID(o_id) !in toactivate_td_ids && FD_ID(o_id) !in toactivate_fd_ids && DO_ID(o_id) !in toactivate_do_ids
{
    assert forall o_id, s_id1, s_id2 :: 
        s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
        DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
        ==> s_id1 == s_id2;

    Lemma_SameObjsOwnershipInSuccessiveStates_SlimState(k, k'_subjects, k'_objects);
    if(TD_ID(o_id) in toactivate_td_ids)
    {
        assert exists s_id2 :: s_id2 in toactivate_s_ids && TD_ID(o_id) in OwnedTDs(k, s_id2);
        var s_id2 :| s_id2 in toactivate_s_ids && TD_ID(o_id) in OwnedTDs(k, s_id2);
        assert DoOwnObj(k, s_id2, o_id);

        assert DoOwnObj_SlimState(k'_subjects, s_id, o_id);
        assert DoOwnObj(k, s_id, o_id);

        // Show conflict
        assert s_id2 == s_id;
        assert s_id2 !in toactivate_s_ids;
    }

    if(FD_ID(o_id) in toactivate_fd_ids)
    {
        assert exists s_id2 :: s_id2 in toactivate_s_ids && FD_ID(o_id) in OwnedFDs(k, s_id2);
        var s_id2 :| s_id2 in toactivate_s_ids && FD_ID(o_id) in OwnedFDs(k, s_id2);
        assert DoOwnObj(k, s_id2, o_id);

        assert DoOwnObj_SlimState(k'_subjects, s_id, o_id);
        assert DoOwnObj(k, s_id, o_id);

        // Show conflict
        assert s_id2 == s_id;
        assert s_id2 !in toactivate_s_ids;
    }

    if(DO_ID(o_id) in toactivate_do_ids)
    {
        assert exists s_id2 :: s_id2 in toactivate_s_ids && DO_ID(o_id) in OwnedDOs(k, s_id2);
        var s_id2 :| s_id2 in toactivate_s_ids && DO_ID(o_id) in OwnedDOs(k, s_id2);
        assert DoOwnObj(k, s_id2, o_id);

        assert DoOwnObj_SlimState(k'_subjects, s_id, o_id);
        assert DoOwnObj(k, s_id, o_id);

        // Show conflict
        assert s_id2 == s_id;
        assert s_id2 !in toactivate_s_ids;
    }
}

lemma Lemma_ExternalObjsActivate_AllObjsToBeDeactivatedAreExternalObjs(
    k:State,
    toactivate_td_ids:set<TD_ID>, toactivate_fd_ids:set<FD_ID>, toactivate_do_ids:set<DO_ID>
)
    requires IsValidState(k) && IsSecureState(k)
    requires forall s_id, o_id :: s_id in AllSubjsIDs(k.subjects) &&
                    (TD_ID(o_id) in toactivate_td_ids || FD_ID(o_id) in toactivate_fd_ids || DO_ID(o_id) in toactivate_do_ids)
                ==> !DoOwnObj(k, s_id, o_id)
        // Requirement: no subject owns these external objects

    ensures forall s_id :: s_id in AllSubjsIDs(k.subjects)
            ==> OwnedTDs(k, s_id) * toactivate_td_ids == {} &&
                OwnedFDs(k, s_id) * toactivate_fd_ids == {} &&
                OwnedDOs(k, s_id) * toactivate_do_ids == {}

    ensures {} <= AllSubjsIDs(k.subjects)
{
    forall s_id | s_id in AllSubjsIDs(k.subjects)
        ensures OwnedTDs(k, s_id) * toactivate_td_ids == {}
        ensures OwnedFDs(k, s_id) * toactivate_fd_ids == {}
        ensures OwnedDOs(k, s_id) * toactivate_do_ids == {}
    {
        assert forall td_id :: td_id in toactivate_td_ids
                ==> !DoOwnObj(k, s_id, td_id.oid);
        assert forall fd_id :: fd_id in toactivate_fd_ids
                ==> !DoOwnObj(k, s_id, fd_id.oid);
        assert forall do_id :: do_id in toactivate_do_ids
                ==> !DoOwnObj(k, s_id, do_id.oid);

        assert forall td_id :: td_id in toactivate_td_ids
                ==> td_id !in OwnedTDs(k, s_id);
        assert forall fd_id :: fd_id in toactivate_fd_ids
                ==> fd_id !in OwnedFDs(k, s_id);
        assert forall do_id :: do_id in toactivate_do_ids
                ==> do_id !in OwnedDOs(k, s_id);
    }

    Lemma_EmptySetIsSubsetOfAnySet(AllSubjsIDs(k.subjects));
}
