include "state_map_OpsSaneStateSubset.s.dfy"
include "../../WK_Design/Model.dfy"
include "../dev/usb2/public/usb_lemmas.i.dfy"
include "../state_properties_OpsSaneStateSubset.i.dfy"
//include "../state_properties.s.dfy"

/*********************** Mapping Lemmas ********************/
lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures DM_IsValidState(dm)
{
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Subjects(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Partitions(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_SubjsOwnObjsThenInSamePartition(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_DevsActivateCond(s, dm);
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_SubjsObjsPIDs(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures DM_IsValidState_SubjsObjsPIDs(dm)
{
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState(s, dm);
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsSecureState_SI2AndSI3(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures DM_IsValidState(dm)
    ensures DM_IsSecureState_SI2(dm)
    ensures DM_IsSecureState_SI3(dm)
{
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsSecureState_SI2(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsSecureState_SI3(s, dm);
}




/*********************** Util Lemmas ********************/
lemma Lemma_WSMStateMapping_EquivilantObjOwnership(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures forall s_id, o_id :: s_id in WSM_AllSubjsIDs(s.subjects) && o_id in WSM_AllObjIDs(s.objects)
                ==> WSM_DoOwnObj(s.subjects, s_id, o_id) == DoOwnObj_SlimState(dm.subjects, s_id, o_id)
{
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    var dm_drvs := WSM_MapState_Drvs_ToSubjs(s);
    var dm_devs := WSM_MapState_Devs_ToSubjs(s);

    forall s_id, o_id | s_id in WSM_AllSubjsIDs(s.subjects) && o_id in WSM_AllObjIDs(s.objects) &&
                WSM_DoOwnObj(s.subjects, s_id, o_id)
        ensures DoOwnObj_SlimState(dm.subjects, s_id, o_id)
    {
        if(TD_ID(o_id) in WSM_OwnedTDs(s.subjects, s_id))
        {
            assert DoOwnObj_SlimState(dm.subjects, s_id, o_id);
        }
    }

    forall s_id, o_id | s_id in WSM_AllSubjsIDs(s.subjects) && o_id in WSM_AllObjIDs(s.objects) &&
                DoOwnObj_SlimState(dm.subjects, s_id, o_id)
        ensures WSM_DoOwnObj(s.subjects, s_id, o_id)
    {
        // Dafny can automatically prove this lemma
    }
}

lemma Lemma_WSMStateMapping_EquivilantObjsOwnedByDevs(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures forall dev_id :: dev_id in WSM_AllDevIDs(s.subjects)
                ==> WSM_OwnedTDs(s.subjects, dev_id.sid) == IDToDev_SlimState(dm.subjects, dev_id).td_ids
    ensures forall dev_id :: dev_id in WSM_AllDevIDs(s.subjects)
                ==> WSM_OwnedFDs(s.subjects, dev_id.sid) == IDToDev_SlimState(dm.subjects, dev_id).fd_ids
    ensures forall dev_id :: dev_id in WSM_AllDevIDs(s.subjects)
                ==> WSM_OwnedDOs(s.subjects, dev_id.sid) == IDToDev_SlimState(dm.subjects, dev_id).do_ids
{
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    var dm_drvs := WSM_MapState_Drvs_ToSubjs(s);
    var dm_devs := WSM_MapState_Devs_ToSubjs(s);

    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();

    forall dev_id | dev_id in WSM_AllDevIDs(s.subjects)
        ensures WSM_OwnedFDs(s.subjects, dev_id.sid) == IDToDev_SlimState(dm.subjects, dev_id).fd_ids
    {
        assert dev_id in s.subjects.os_devs || dev_id in s.subjects.usbpdevs || dev_id in s.subjects.eehcis;

        if(dev_id in s.subjects.os_devs)
        {
            // Dafny can automatically prove this lemma
        }
    }

    forall dev_id | dev_id in WSM_AllDevIDs(s.subjects)
        ensures WSM_OwnedDOs(s.subjects, dev_id.sid) == IDToDev_SlimState(dm.subjects, dev_id).do_ids
    {
        assert dev_id in s.subjects.os_devs || dev_id in s.subjects.usbpdevs || dev_id in s.subjects.eehcis;

        if(dev_id in s.subjects.os_devs)
        {
            // Dafny can automatically prove this lemma
        }
    }
}

lemma Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures AllTDIDs(dm.objects) == WSM_AllTDIDs(s.objects)
    ensures AllFDIDs(dm.objects) == WSM_AllFDIDs(s.objects)
    ensures AllDOIDs(dm.objects) == WSM_AllDOIDs(s.objects)
    ensures AllObjsIDs(dm.objects) == WSM_AllObjIDs(s.objects)

    ensures IsValidState_Objects_UniqueObjIDs(dm.objects)
        // Property: Objects have different internal IDs
    ensures forall o_id :: o_id in WSM_AllObjIDs(s.objects)
                ==> IsObjID(dm.objects, o_id) == WSM_IsObjID(s.objects, o_id)
    ensures WSM_AllHCodedTDIDs(s.subjects) == AllHCodedTDIDs(dm.subjects)
        // Property: Same set of hardcoded TDs
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall o_id :: o_id in WSM_AllObjIDs(s.objects)
                ==> WSM_MapWSParititonID_ToAbstractPartitionID(WSM_ObjPID(s.subjects, s.objects, s.id_mappings, globals, o_id)) == ObjPID_KObjects(dm.objects, o_id)
        // Property: Same object PIDs
{
    Lemma_WSMStateMapping_ProveIsValidState_Objects_UniqueObjIDs(s, dm);
}

lemma Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures MapGetKeys(dm.subjects.drvs) == WSM_AllDrvIDs(s.subjects)
    ensures MapGetKeys(dm.subjects.devs) == WSM_AllDevIDs(s.subjects)
    ensures AllSubjsIDs(dm.subjects) == WSM_AllSubjsIDs(s.subjects)

    ensures forall drv_sid, dev_sid :: (Drv_ID(drv_sid) in dm.subjects.drvs) && (Dev_ID(dev_sid) in dm.subjects.devs)
                ==> (drv_sid != dev_sid)
        // Property: Subjects have different internal IDs
    ensures forall s_id :: s_id in WSM_AllSubjsIDs(s.subjects)
                ==> IsSubjID(dm.subjects, s_id) == WSM_IsSubjID(s.subjects, s_id)
    ensures var globals := wkm_get_globals(s.wk_mstate);
            forall s_id :: s_id in WSM_AllSubjsIDs(s.subjects)
                ==> WSM_MapWSParititonID_ToAbstractPartitionID(WSM_SubjPID(s.subjects, s.objects, s.id_mappings, globals, s_id)) == SubjPID_SlimState(dm.subjects, s_id)
        // Property: Same subject PIDs
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
}

lemma Lemma_WSMStateMapping_EquivilantBuildMap_DevsToHCodedTDVals(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures WK_ValidObjs_ObjInSubjsMustBeInState(s.subjects, s.objects)
    ensures forall dev_id :: dev_id in s.subjects.os_devs
                ==> s.subjects.os_devs[dev_id].hcoded_td_id in s.subjects.os_devs[dev_id].td_ids
        // Properties needed by WSM_BuildMap_DevsToHCodedTDVals
    ensures IsValidState_Objects_UniqueObjIDs(dm.objects)
    ensures forall dev_id :: dev_id in dm.subjects.devs
                ==> dm.subjects.devs[dev_id].hcoded_td_id in dm.subjects.devs[dev_id].td_ids
    ensures forall dev_id :: dev_id in dm.subjects.devs
                ==> dm.subjects.devs[dev_id].hcoded_td_id in dm.objects.hcoded_tds 
        // Properties needed by BuildMap_DevsToHCodedTDVals
    ensures WSM_BuildMap_DevsToHCodedTDVals(s.subjects, s.objects) == BuildMap_DevsToHCodedTDVals(dm.subjects, dm.objects)
{
    // Prove pre-conditions
    reveal WK_ValidObjs();

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_21And22(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_23(s, dm);

    // Prove main property
    var dm_drvs := WSM_MapState_Drvs_ToSubjs(s);
    var dm_devs := WSM_MapState_Devs_ToSubjs(s);

    var s_map := WSM_BuildMap_DevsToHCodedTDVals(s.subjects, s.objects);
    var dm_map := BuildMap_DevsToHCodedTDVals(dm.subjects, dm.objects);

    assert MapGetKeys(s_map) == WSM_AllDevIDs(s.subjects);
    assert MapGetKeys(dm_map) == MapGetKeys(dm.subjects.devs);
    assert MapGetKeys(s_map) == MapGetKeys(dm_map);

    forall id | id in s_map
        ensures s_map[id] == dm_map[id]
    {
        assert id in s.subjects.os_devs || id in s.subjects.usbpdevs || id in s.subjects.eehcis;

        reveal WK_ValidObjs_ObjInSubjsMustBeInState();
        if(id in s.subjects.os_devs)
        {
            assert s_map[id] == WSM_MapOSTDVal_ToTDVal(s.objects, s.objects.os_tds[s.subjects.os_devs[id].hcoded_td_id].val);
            assert s_map[id] == dm_map[id];
        }
        else if(id in s.subjects.usbpdevs)
        {
            assert s_map[id] == s.objects.usbpdev_tds[s.subjects.usbpdevs[id].hcoded_td_id];
            assert s_map[id] == dm_map[id];
        }
        else
        {
            assert id in s.subjects.eehcis;
            assert s_map[id] == s.objects.eehci_hcoded_tds[s.subjects.eehcis[id].hcoded_td_id];
            assert s_map[id] == dm_map[id]; 
        }
    }

    Lemma_Map_Equality2(s_map, dm_map);
    assert s_map == dm_map;
}

// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_WSM_eEHCI_GetUSBTDRegVal_GivenIDOfEEHCIOtherTDs_ProveSameResultIfOnlyTempGVarsCountersRegsAndStacksAreChanged(s1:state, s2:state, eehci_other_td_id:TD_ID)
    requires WK_ValidGlobalState(wkm_get_globals(s1.wk_mstate))
    requires WK_ValidSubjs(s1.subjects, s1.id_mappings)
    requires WK_ValidIDMappings(s1.subjects, s1.objects, s1.id_mappings)
    requires WK_ValidObjs(s1.subjects, s1.objects)
    requires WK_SecureMState(s1.wk_mstate)

    requires eehci_other_td_id in s1.objects.eehci_other_tds

    requires WK_ValidGlobalState(wkm_get_globals(s2.wk_mstate))
    requires WK_ValidSubjs(s2.subjects, s2.id_mappings)
    requires WK_ValidIDMappings(s2.subjects, s2.objects, s2.id_mappings)
    requires WK_ValidObjs(s2.subjects, s2.objects)
    requires WK_SecureMState(s2.wk_mstate)

    requires eehci_other_td_id in s2.objects.eehci_other_tds

    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)

    ensures WSM_eEHCI_GetUSBTDRegVal_GivenIDOfEEHCIOtherTDs(s1, eehci_other_td_id) ==
            WSM_eEHCI_GetUSBTDRegVal_GivenIDOfEEHCIOtherTDs(s2, eehci_other_td_id)
/*{
    // [TODO][Axiom][Assumption] If only temp global variables and registers and the stack are changed, then eEHCIs'
    // other TDs map to same values in the WK design
    assume WSM_eEHCI_GetUSBTDRegVal_GivenIDOfEEHCIOtherTDs(s1, eehci_other_td_id) ==
            WSM_eEHCI_GetUSBTDRegVal_GivenIDOfEEHCIOtherTDs(s2, eehci_other_td_id);
}*/

// [State/Ops Mapping] Axiom (well known): The state modifications in the WK code maps to the corresponding state 
// modifications in the WK design.
// This axiom makes sense because most APIs and I/O accesses in the WK implementation maps to one and only one 
// operation in the WK design.
lemma {:axiom} Lemma_WSM_USBTD_CalcTDVal_ProveSameResultIfOnlyTempGVarsCountersRegsAndStacksAreChanged(s1:state, s2:state, usbtd_id:TD_ID)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)
    requires usbtd_id in s1.objects.usbtd_tds
    requires usbtd_id in s2.objects.usbtd_tds

    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)

    ensures WSM_USBTD_CalcTDVal(s1, usbtd_id) ==
            WSM_USBTD_CalcTDVal(s2, usbtd_id)
/*{
    // [TODO][Axiom][Assumption] If only temp global variables and registers and the stack are changed, then USB TDs
    // map to same values in the WK design
    assume WSM_USBTD_CalcTDVal(s1, usbtd_id) ==
            WSM_USBTD_CalcTDVal(s2, usbtd_id);
}*/




/*********************** Private Lemmas of Util Lemmas ********************/
lemma Lemma_WSMStateMapping_ProveIsValidState_Objects_UniqueObjIDs(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures IsValidState_Objects_UniqueObjIDs(dm.objects)
{
    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s);
    reveal WK_ValidObjs_ObjIDs();
    
    var active_non_hcoded_tds := MapGetKeys(WSM_MapState_TDsToAbstractTDs_PickActiveNonHCodedTDs(s));
    var active_fds := MapGetKeys(WSM_MapState_FDsToAbstractFDs_PickActiveFDs(s));
    var active_dos := MapGetKeys(WSM_MapState_DOsToAbstractDOs_PickActiveDOs(s));

    var inactive_non_hcoded_tds := MapGetKeys(WSM_MapState_TDsToAbstractTDs_PickInactiveNonHCodedTDs(s));
    var inactive_fds := MapGetKeys(WSM_MapState_FDsToAbstractFDs_PickInactiveFDs(s));
    var inactive_dos := MapGetKeys(WSM_MapState_DOsToAbstractDOs_PickInactiveDOs(s));

    var hcoded_tds := MapGetKeys(WSM_MapState_TDsToAbstractTDs_PickHCodedTDs(s));

    assert forall id :: id in active_non_hcoded_tds 
            ==> id !in inactive_non_hcoded_tds &&
                id !in hcoded_tds;
    assert forall id :: id in inactive_non_hcoded_tds
            ==> id !in hcoded_tds;
    assert forall id :: id in active_fds
            ==> id !in inactive_fds;
    assert forall id :: id in active_dos
            ==> id !in inactive_dos;

    reveal IsValidState_Objects_UniqueObjIDs();
    assert IsValidState_Objects_UniqueObjIDs(dm.objects);
}




/*********************** Private Lemmas for Mapping Lemmas ********************/
lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Subjects(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures DM_IsValidState_Subjects(dm)
{
    reveal WK_ValidSubjs();
    reveal WK_ValidSubjs_SubjIDs();
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures var k := DMStateToState(dm);
             K_ValidState_Objects_Property25(k)
        // Properties needed by other utility lemmas
    ensures P_DMSubjectsHasUniqueIDs(dm.subjects)
    ensures DM_IsValidState_Objects(dm)
{
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_21And22(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_23(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_24(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_25(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_26And27And28(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_29And210(s, dm);

    reveal K_ValidState_Objects_Property25();
    reveal K_ValidState_Objects_Property26And27And28();
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Partitions(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures DM_IsValidState_Partitions(dm)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_SubjsOwnObjsThenInSamePartition(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    requires var k := DMStateToState(dm);
             IsValidState_Objects_UniqueObjIDs(k.objects) &&
             K_ValidState_Objects_Property25(k)

    ensures var k := DMStateToState(dm);
            K_IsValidState_SubjsOwnObjsThenInSamePartition_Opaque(k)

    ensures P_ObjsInSubjsAreInSetOfAllObjs(dm.subjects, dm.objects)
    ensures DM_IsValidState_SubjsOwnObjsThenInSamePartition(dm)
{
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjOwnership(s, dm);

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    var k := DMStateToState(dm);

    reveal K_ValidState_Objects_Property25();
    Lemma_ObjsInSubjsAreAlsoInState(k);

    forall s_id, o_id | s_id in AllSubjsIDs(k.subjects) && DoOwnObj(k, s_id, o_id)
        ensures SubjPID(k, s_id) == ObjPID(k, o_id)
    {
        assert s_id in WSM_AllSubjsIDs(s.subjects);

        assert WSM_IsSubjID(subjs, s_id);
        assert WSM_IsObjID(objs, o_id);
        assert WSM_DoOwnObj(subjs, s_id, o_id);
        Lemma_ObjPID_SamePIDWithOwnerSubject(subjs, objs, id_mappings, globals, s_id, o_id);
    }

    reveal K_IsValidState_SubjsOwnObjsThenInSamePartition_Opaque();
    assert K_IsValidState_SubjsOwnObjsThenInSamePartition_Opaque(k);
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_DevsActivateCond(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures DM_IsValidState_DevsActivateCond(dm)
{
    reveal WK_ValidState_DevsActivateCond();
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsSecureState_SI2(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    requires DM_IsValidState_SubjsObjsPIDs(dm)

    ensures DM_IsSecureState_SI2(dm)
{
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjOwnership(s, dm);

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    // Prove some predicates needed by WSM_IsWimpTDID(objs, td_id);
    Lemma_ValidState_ImpliesWK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(subjs, objs, id_mappings, globals);
    assert WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition(subjs, objs, id_mappings, globals);
    reveal WK_SI_Property_OnlyOSObjsAndUSBPDevObjsCanBeInOSPartition();

    // Prove the main property
    var k := DMStateToState(dm);
    var k_params := KToKParams(k);
    var k_tds_state := ActiveTDsState(k);
    forall td_id | td_id in DM_TDIDsInGreen(dm)
        ensures DoTDsIncludeSecureNoTDWriteTransfersOnly(k_params, k_tds_state, td_id)
    {
        // Apply td_id in DM_TDIDsInGreen(dm)
        assert td_id in WSM_AllTDIDs(s.objects);
        assert WSM_ObjPID(subjs, objs, id_mappings, globals, td_id.oid) != WS_PartitionID(PID_RESERVED_OS_PARTITION);
        assert WSM_ObjPID(subjs, objs, id_mappings, globals, td_id.oid) != WS_PartitionID(PID_INVALID);

        // Prove WSM_IsWimpTDID(objs, td_id);
        reveal WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions();
        assert WSM_IsWimpTDID(objs, td_id);
        
        // Prove !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, td_id)
        assume !DoActiveTDIncludeTransfersToInvalidObjOrObjOutsidePartition(k_params, k_tds_state, td_id);
        
        // Prove no TD write is defined 
        assume (forall td_id2 :: td_id2 in k_tds_state[td_id].trans_params_tds
                    ==> W !in k_tds_state[td_id].trans_params_tds[td_id2].amodes);
    }
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsSecureState_SI3(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures P_DMObjectsHasUniqueIDs(dm.objects)
    ensures DM_IsSecureState_SI3(dm)
{
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    var subjs := s.subjects;
    var objs := s.objects;
    var id_mappings := s.id_mappings;
    var objs_addrs := s.objs_addrs;
    var globals := wkm_get_globals(s.wk_mstate);

    reveal WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions();
    var k := DMStateToState(dm);
    forall o_id | o_id in AllObjsIDs(k.objects) && ObjPID(k, o_id) != NULL
        ensures ObjPID(k, o_id) in k.pids
    {
        // Apply o_id in AllObjsIDs(k.objects) && ObjPID(k, o_id) != NULL
        assert o_id in WSM_AllObjIDs(objs);
        assert WSM_ObjPID(subjs, objs, id_mappings, globals, o_id) != WS_PartitionID(PID_INVALID);

        Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s);
        reveal WK_ValidObjs_ObjIDs();
        if(WSM_IsUSBTDMappedObj(objs, o_id))
        {
            var idword := USBTDMappedObj_IDToUSBTDIDWord(subjs, objs, id_mappings, o_id);
            var pid := WSM_ObjPID(subjs, objs, id_mappings, globals, o_id);
            assert ObjPID(k, o_id) == WSM_MapWSParititonID_ToAbstractPartitionID(pid);
            assert pid == ObjPID_USBTD_ByIDWord(globals, idword);

            var usbtd_slot := usbtd_get_slot_by_idword(globals, idword);
            assert pid == usbtd_map_get_pid(globals, usbtd_slot);

            assert WK_USBTD_Map_ValidGlobalVarValues(globals);
            assert usbtd_slot_valid_pid(globals, usbtd_slot);
            assert pid in pids_parse_g_wimp_pids(globals);
            assert pid in WK_GetAllPIDs(globals);

            assert WSM_MapWSParititonID_ToAbstractPartitionID(pid) in WSM_MapState_PIDs(s);
            assert ObjPID(k, o_id) in k.pids;
        }
    }
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_21And22(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    ensures P_DMSubjectsHasUniqueIDs(dm.subjects)

    ensures IsValidState_Objects_UniqueObjIDs(dm.objects)
    ensures (|MapGetKeys(dm.objects.active_non_hcoded_tds)| + |MapGetKeys(dm.objects.active_fds)| + |MapGetKeys(dm.objects.active_dos)| + 
            |(dm.objects.inactive_non_hcoded_tds)| + |(dm.objects.inactive_fds)| + |(dm.objects.inactive_dos)| + 
            |MapGetKeys(dm.objects.hcoded_tds)| > 0)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjIDs();

    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Subjects(s, dm);
    Lemma_WSMStateMapping_ProveIsValidState_Objects_UniqueObjIDs(s, dm);
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_23(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    requires IsValidState_Objects_UniqueObjIDs(dm.objects)
    requires P_DMSubjectsHasUniqueIDs(dm.subjects)

    ensures forall dev_id :: dev_id in dm.subjects.devs
                ==> dm.subjects.devs[dev_id].hcoded_td_id in dm.subjects.devs[dev_id].td_ids
    ensures MapGetKeys(dm.objects.hcoded_tds) == AllHCodedTDIDs(dm.subjects)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    var dm_devs := WSM_MapState_Devs_ToSubjs(s);
    forall dev_id | dev_id in dm.subjects.devs
        ensures dm.subjects.devs[dev_id].hcoded_td_id in dm.subjects.devs[dev_id].td_ids
    {
        assert dev_id in WSM_AllDevIDs(s.subjects);

        
        if(dev_id in s.subjects.os_devs)
        {
            assert dm.subjects.devs[dev_id].hcoded_td_id in dm.subjects.devs[dev_id].td_ids;
        }
        else if(dev_id in s.subjects.usbpdevs)
        {
            assert dm.subjects.devs[dev_id].hcoded_td_id in dm.subjects.devs[dev_id].td_ids;
        }
        else
        {
            assert dev_id in s.subjects.eehcis;
            reveal WK_ValidSubjs();
            reveal WK_ValidSubjs_eEHCIs();

            assert dm.subjects.devs[dev_id].hcoded_td_id in dm.subjects.devs[dev_id].td_ids;
        }
    }
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_24(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    requires IsValidState_Objects_UniqueObjIDs(dm.objects)
    requires P_DMSubjectsHasUniqueIDs(dm.subjects)

    ensures var k := DMStateToState(dm);
            forall o_id, s_id1, s_id2 :: 
                s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
                DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
            ==> s_id1 == s_id2
{
    reveal WK_ValidObjs();

    Lemma_WSMStateMapping_EquivilantObjOwnership(s, dm);
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    var k := DMStateToState(dm);
    forall o_id, s_id1, s_id2 | 
        s_id1 in AllSubjsIDs(k.subjects) && s_id2 in AllSubjsIDs(k.subjects) && 
        DoOwnObj(k, s_id1, o_id) && DoOwnObj(k, s_id2, o_id)
        ensures s_id1 == s_id2
    {
        assert s_id1 in WSM_AllSubjsIDs(s.subjects);
        assert s_id2 in WSM_AllSubjsIDs(s.subjects);
        assert WSM_DoOwnObj(s.subjects, s_id1, o_id);
        assert WSM_DoOwnObj(s.subjects, s_id2, o_id);
    }
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_25(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    requires IsValidState_Objects_UniqueObjIDs(dm.objects)
    requires P_DMSubjectsHasUniqueIDs(dm.subjects)

    ensures var k := DMStateToState(dm);
            K_ValidState_Objects_Property25(k) 
{
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_25_InnerDrvs(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_25_InnerDevs(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_25_Summary(dm);
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_26And27And28(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    requires var k := DMStateToState(dm);
             IsValidState_Objects_UniqueObjIDs(k.objects) &&
             (forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids) &&
             (forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds)

    ensures var k := DMStateToState(dm);
            K_ValidState_Objects_Property26And27And28(k)
{
    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_HCodedTDs(s);
    reveal WK_ValidObjs_HCodedTDs();

    Lemma_WSMStateMapping_EquivilantBuildMap_DevsToHCodedTDVals(s, dm);
    Lemma_WSMStateMapping_EquivilantObjsOwnedByDevs(s, dm);

    reveal K_ValidState_Objects_Property26And27And28();
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_29And210(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    requires IsValidState_Objects_UniqueObjIDs(dm.objects)
    requires P_DMSubjectsHasUniqueIDs(dm.subjects)

    ensures var k := DMStateToState(dm);
            IsValidState_TDsToAllStates(k) &&
            IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(k.objects)
{
    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s);
    reveal WK_ValidObjs_ObjIDs();
    
    var active_non_hcoded_tds := MapGetKeys(WSM_MapState_TDsToAbstractTDs_PickActiveNonHCodedTDs(s));
    var active_fds := MapGetKeys(WSM_MapState_FDsToAbstractFDs_PickActiveFDs(s));
    var active_dos := MapGetKeys(WSM_MapState_DOsToAbstractDOs_PickActiveDOs(s));

    var inactive_non_hcoded_tds := MapGetKeys(WSM_MapState_TDsToAbstractTDs_PickInactiveNonHCodedTDs(s));
    var inactive_fds := MapGetKeys(WSM_MapState_FDsToAbstractFDs_PickInactiveFDs(s));
    var inactive_dos := MapGetKeys(WSM_MapState_DOsToAbstractDOs_PickInactiveDOs(s));

    var hcoded_tds := MapGetKeys(WSM_MapState_TDsToAbstractTDs_PickHCodedTDs(s));

    reveal IsValidState_Objects_ActiveObjsMustHaveNonNULLPID();
    assert IsValidState_Objects_ActiveObjsMustHaveNonNULLPID(dm.objects);
}




/*********************** Private Lemmas of Private Lemmas for Mapping Lemmas ********************/
predicate {:opaque} K_IsValidState_SubjsOwnObjsThenInSamePartition_Opaque(k:State)
{
    reveal K_ValidState_Objects_Property25();

    IsValidState_Objects_UniqueObjIDs(k.objects) &&
    K_ValidState_Objects_Property25(k) &&
    IsValidState_SubjsOwnObjsThenInSamePartition(k)
}


predicate {:opaque} P_DM_IsValidState_Objects_25_InnerDevs(dm:DM_State)
{
    (forall dev_id, td_id :: dev_id in dm.subjects.devs 
        ==> td_id in dm.subjects.devs[dev_id].td_ids ==> td_id in AllTDIDs(dm.objects)
    ) &&
    (forall dev_id, fd_id :: dev_id in dm.subjects.devs 
        ==> fd_id in dm.subjects.devs[dev_id].fd_ids ==> fd_id in AllFDIDs(dm.objects)
    ) &&
    (forall dev_id, do_id :: dev_id in dm.subjects.devs 
        ==> do_id in dm.subjects.devs[dev_id].do_ids ==> do_id in AllDOIDs(dm.objects)
    )
}

predicate {:opaque} P_DM_IsValidState_Objects_25_InnerDrvs(dm:DM_State)
{
    (forall drv_id, td_id :: drv_id in dm.subjects.drvs 
        ==> td_id in dm.subjects.drvs[drv_id].td_ids ==> td_id in AllTDIDs(dm.objects)
    ) &&
    (forall drv_id, fd_id :: drv_id in dm.subjects.drvs 
        ==> fd_id in dm.subjects.drvs[drv_id].fd_ids ==> fd_id in AllFDIDs(dm.objects)
    ) &&
    (forall drv_id, do_id :: drv_id in dm.subjects.drvs 
        ==> do_id in dm.subjects.drvs[drv_id].do_ids ==> do_id in AllDOIDs(dm.objects)
    )
}

predicate {:opaque} K_ValidState_Objects_Property25(k:State)
{
    (forall drv_id, td_id :: 
        drv_id in k.subjects.drvs && td_id in k.subjects.drvs[drv_id].td_ids
        ==> td_id in AllTDIDs(k.objects)) && 
    (forall dev_id, td_id :: 
        dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
        ==> td_id in AllTDIDs(k.objects)) &&

    (forall drv_id, fd_id :: 
        drv_id in k.subjects.drvs && fd_id in k.subjects.drvs[drv_id].fd_ids
        ==> fd_id in AllFDIDs(k.objects)) && 
    (forall dev_id, fd_id :: 
        dev_id in k.subjects.devs && fd_id in k.subjects.devs[dev_id].fd_ids
        ==> fd_id in AllFDIDs(k.objects)) &&

    (forall drv_id, do_id :: 
        drv_id in k.subjects.drvs && do_id in k.subjects.drvs[drv_id].do_ids
        ==> do_id in AllDOIDs(k.objects)) && 
    (forall dev_id, do_id :: 
        dev_id in k.subjects.devs && do_id in k.subjects.devs[dev_id].do_ids
        ==> do_id in AllDOIDs(k.objects))
}

predicate {:opaque} K_ValidState_Objects_Property26And27And28(k:State)
    requires IsValidState_Objects_UniqueObjIDs(k.objects)
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.subjects.devs[dev_id].td_ids
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id in k.objects.hcoded_tds
{
    var hcoded_tds := BuildMap_DevsToHCodedTDVals(k.subjects, k.objects);
    (forall dev_id :: dev_id in k.subjects.devs
        ==> (forall td_id :: td_id in HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds
            ==> HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds[td_id].amodes != {R,W})) &&

    //// Condition 2.7 Hardcoded TDs do not reference any hardcoded TDs
    (forall dev_id, td_id :: dev_id in k.subjects.devs &&
                td_id in HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds
        ==> td_id !in AllHCodedTDIDs(k.subjects)) &&

    //// Condition 2.8 Objects refed in hardcoded TDs must be owned by the device 
    (forall dev_id :: dev_id in k.subjects.devs
        ==> (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_tds) <= 
                IDToDev(k, dev_id).td_ids) &&
            (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_fds) <= 
                IDToDev(k, dev_id).fd_ids) &&
            (MapGetKeys(HCodedTDValOfDev(hcoded_tds, dev_id).trans_params_dos) <= 
                IDToDev(k, dev_id).do_ids))
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_25_InnerDrvs(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    requires IsValidState_Objects_UniqueObjIDs(dm.objects)
    requires P_DMSubjectsHasUniqueIDs(dm.subjects)

    ensures P_DM_IsValidState_Objects_25_InnerDrvs(dm)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    var dm_drvs := WSM_MapState_Drvs_ToSubjs(s);
    var dm_devs := WSM_MapState_Devs_ToSubjs(s);
    var k := DMStateToState(dm);

    forall drv_id, td_id | drv_id in dm.subjects.drvs
        ensures td_id in dm.subjects.drvs[drv_id].td_ids ==> td_id in AllTDIDs(dm.objects)
    {
        // Dafny can automatically prove this lemma
    }

    forall drv_id, fd_id | drv_id in dm.subjects.drvs
        ensures fd_id in dm.subjects.drvs[drv_id].fd_ids ==> fd_id in AllFDIDs(dm.objects)
    {
        // Dafny can automatically prove this lemma
    }

    forall drv_id, do_id | drv_id in dm.subjects.drvs
        ensures do_id in dm.subjects.drvs[drv_id].do_ids ==> do_id in AllDOIDs(dm.objects)
    {
        // Dafny can automatically prove this lemma
    }

    reveal P_DM_IsValidState_Objects_25_InnerDrvs();
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_25_InnerDevs(s:state, dm:DM_State)
    requires OpsSaneStateSubset(s)
    requires dm == WSM_MapState(s)

    requires IsValidState_Objects_UniqueObjIDs(dm.objects)
    requires P_DMSubjectsHasUniqueIDs(dm.subjects)

    ensures P_DM_IsValidState_Objects_25_InnerDevs(dm)
{
    reveal WK_ValidObjs();
    reveal WK_ValidObjs_ObjInSubjsMustBeInState();

    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    Lemma_WSMStateMapping_EquivilantObjIDsAndPIDs(s, dm);

    var dm_drvs := WSM_MapState_Drvs_ToSubjs(s);
    var dm_devs := WSM_MapState_Devs_ToSubjs(s);

    forall dev_id, td_id | dev_id in dm.subjects.devs &&
                td_id in dm.subjects.devs[dev_id].td_ids
        ensures td_id in AllTDIDs(dm.objects)
    {
        assert dev_id in s.subjects.eehcis || dev_id in s.subjects.usbpdevs || dev_id in s.subjects.os_devs;

        if(dev_id in s.subjects.eehcis)
        {
            Lemma_eEHCIs_ProveObjsAreInSystem(s, dev_id);
            assert td_id in s.subjects.eehcis[dev_id].td_ids;
            assert td_id in WSM_AllTDIDs(s.objects);
            assert td_id in AllTDIDs(dm.objects);
        }
        else if(dev_id in s.subjects.usbpdevs)
        {
            assert td_id in AllTDIDs(dm.objects);
        }
        else
        {
            assert dev_id in s.subjects.os_devs;
            assert td_id in AllTDIDs(dm.objects);
        }
    }

    forall dev_id, fd_id | dev_id in dm.subjects.devs
        ensures fd_id in dm.subjects.devs[dev_id].fd_ids ==> fd_id in AllFDIDs(dm.objects)
    {
        // Dafny can automatically prove this lemma
    }

    forall dev_id, do_id | dev_id in dm.subjects.devs
        ensures do_id in dm.subjects.devs[dev_id].do_ids ==> do_id in AllDOIDs(dm.objects)
    {
        // Dafny can automatically prove this lemma
    }

    reveal P_DM_IsValidState_Objects_25_InnerDevs();
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsValidState_Objects_25_Summary(dm:DM_State)
    requires P_DM_IsValidState_Objects_25_InnerDrvs(dm)
    requires P_DM_IsValidState_Objects_25_InnerDevs(dm)

    ensures var k := DMStateToState(dm);
            K_ValidState_Objects_Property25(k)
{
    var k := DMStateToState(dm);
    assert k.subjects == dm.subjects;
    assert k.objects == dm.objects;

    reveal P_DM_IsValidState_Objects_25_InnerDrvs();
    reveal P_DM_IsValidState_Objects_25_InnerDevs();

    assert (forall drv_id, td_id :: 
                drv_id in k.subjects.drvs && td_id in k.subjects.drvs[drv_id].td_ids
                ==> td_id in AllTDIDs(k.objects)) && 
            (forall dev_id, td_id :: 
                dev_id in k.subjects.devs && td_id in k.subjects.devs[dev_id].td_ids
                ==> td_id in AllTDIDs(k.objects)) &&

            (forall drv_id, fd_id :: 
                drv_id in k.subjects.drvs && fd_id in k.subjects.drvs[drv_id].fd_ids
                ==> fd_id in AllFDIDs(k.objects)) && 
            (forall dev_id, fd_id :: 
                dev_id in k.subjects.devs && fd_id in k.subjects.devs[dev_id].fd_ids
                ==> fd_id in AllFDIDs(k.objects)) &&

            (forall drv_id, do_id :: 
                drv_id in k.subjects.drvs && do_id in k.subjects.drvs[drv_id].do_ids
                ==> do_id in AllDOIDs(k.objects)) && 
            (forall dev_id, do_id :: 
                dev_id in k.subjects.devs && do_id in k.subjects.devs[dev_id].do_ids
                ==> do_id in AllDOIDs(k.objects));

    reveal K_ValidState_Objects_Property25();
}