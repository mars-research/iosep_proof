include "../state_properties.s.dfy"
include "state_map_OpsSaneStateSubset.i.dfy"

function WSM_MapSecureState(s:state) : (dm:DM_State)
    requires OpsSaneState(s)

    ensures DM_IsValidState(dm) 
    ensures DM_IsSecureState(dm) 
{
    var result := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, result);

    result
}

lemma Lemma_SaneWSMState_MapToSecureDMState(s:state, dm:DM_State)
    requires OpsSaneState(s)
    requires dm == WSM_MapState(s)

    ensures DM_IsValidState(dm)
    ensures DM_IsSecureState(dm)
{
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsSecureState_SI2AndSI3(s, dm);
    Lemma_ValidWSMState_MapToDMState_FulfillDM_IsSecureState_SI1(s, dm);
}

lemma Lemma_ValidWSMState_MapToDMState_FulfillDM_IsSecureState_SI1(s:state, dm:DM_State)
    requires OpsSaneState(s)
    requires dm == WSM_MapState(s)

    requires DM_IsValidState_SubjsObjsPIDs(dm)

    ensures DM_IsSecureState_SI1(dm)
{
    reveal WSM_OpsSaneState_Security_SI1();
}

lemma Lemma_SaneWSMState_MapGreenPID(s:state, dm:DM_State, pid:WS_PartitionID)
    requires OpsSaneState(s)
    requires dm == WSM_MapState(s)

    requires pid != WS_PartitionID(PID_INVALID)
    requires pid != WS_PartitionID(PID_RESERVED_OS_PARTITION)

    ensures WSM_MapWSParititonID_ToAbstractPartitionID(pid) != NULL
    ensures WSM_MapWSParititonID_ToAbstractPartitionID(pid) != dm.red_pid
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SaneWSMState_MapSubjNonNULLPID(s:state, dm:DM_State, s_id:Subject_ID)
    requires OpsSaneState(s)
    requires dm == WSM_MapState(s)

    requires WSM_IsSubjID(s.subjects, s_id)
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), s_id) != WS_PartitionID(PID_INVALID)

    ensures DM_IsSubjID(dm.subjects, s_id)
    ensures DM_SubjPID(dm.subjects, s_id) != NULL
{
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
}

lemma Lemma_SaneWSMState_MapSubjGreenPID(s:state, dm:DM_State, s_id:Subject_ID)
    requires OpsSaneState(s)
    requires dm == WSM_MapState(s)

    requires WSM_IsSubjID(s.subjects, s_id)
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), s_id) != WS_PartitionID(PID_INVALID)
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), s_id) != WS_PartitionID(PID_RESERVED_OS_PARTITION)

    ensures DM_IsSubjID(dm.subjects, s_id)
    ensures DM_SubjPID(dm.subjects, s_id) != NULL
    ensures DM_SubjPID(dm.subjects, s_id) != dm.red_pid
{
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
}




/*********************** Lemmas for State Mappings in WK APIs ********************/
lemma Lemma_WKAPI_ChangeTempGVars_MapToSameDMState(s1:state, s2:state)
    requires OpsSaneState(s1)
    requires InstSaneState(s2)

    requires state_equal_except_tempgvar_regs_stack(s1, s2)

    ensures OpsSaneState(s2)
    ensures WSM_MapState(s1) == WSM_MapState(s2)
{
    reveal global_non_scratchpad_vars_are_unchanged();
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s1, s2);
    Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s1, s2);
    Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s1, s2);
    assert OpsSaneStateSubset(s2);

    reveal global_non_scratchpad_vars_except_counters_are_unchanged();
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Subjs(s1, s2);
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs(s1, s2);

    // Apply axioms
    Lemma_F_WSM_MapState_AlwaysExistTDsToAllStates_Property(s1, s2);

    // Prove OpsSaneState(s2)
    reveal WSM_OpsSaneState_Security_SI1();
    assert OpsSaneState(s2);
}

lemma Lemma_WKAPI_ChangeTempGVarsAndCounters_MapToSameDMState(s1:state, s2:state)
    requires OpsSaneState(s1)
    requires InstSaneState(s2)

    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)

    ensures OpsSaneState(s2)
    ensures WSM_MapState(s1) == WSM_MapState(s2)
{
    reveal global_non_scratchpad_vars_except_counters_are_unchanged();
    Lemma_WK_OpsSaneStateSubset_Validity_OSObjsCannotBeActiveInWimpPartitions_IfOSSubjsObjsAreUnchanged(s1, s2);
    Lemma_WK_OpsSaneStateSubset_Validity_LimitationOfUSBTDsVerification_IfUSBTDsAreUnchanged(s1, s2);
    Lemma_WK_OpsSaneStateSubset_Validity_USBTDsInRecordIsEitherEmptyOrSecure_IfUSBTDsAreUnchanged(s1, s2);
    assert OpsSaneStateSubset(s2);

    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Subjs(s1, s2);
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs(s1, s2);

    // Apply axioms
    Lemma_F_WSM_MapState_AlwaysExistTDsToAllStates_Property(s1, s2);

    // Prove OpsSaneState(s2)
    reveal WSM_OpsSaneState_Security_SI1();
    assert OpsSaneState(s2);
}




/*********************** Private Lemmas for State Mappings in WK APIs ********************/
lemma Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Subjs(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)

    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)

    ensures WSM_MapState_Subjs(s1) == WSM_MapState_Subjs(s2)
{
    reveal global_non_scratchpad_vars_except_counters_are_unchanged();
}

lemma Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)

    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)

    ensures WSM_MapState_Objs(s1) == WSM_MapState_Objs(s2)
{
    reveal global_non_scratchpad_vars_except_counters_are_unchanged();

    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs_TDs(s1, s2);
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs_FDs(s1, s2);
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs_DOs(s1, s2);
}

lemma Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs_TDs(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)

    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)

    ensures WSM_MapState_GatherAllAbstractTDs(s1) == WSM_MapState_GatherAllAbstractTDs(s2)
{
    reveal global_non_scratchpad_vars_except_counters_are_unchanged();

    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s1);
    reveal WK_ValidObjs_ObjIDs();

    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs_EEHCIOtherTDs(s1, s2);
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs_USBTDs(s1, s2);
    Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs_OtherTDs(s1, s2);
}

lemma Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs_EEHCIOtherTDs(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)

    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)

    ensures WSM_MapStateToAbstractTDs_ForEEHCIOtherTDs(s1) == WSM_MapStateToAbstractTDs_ForEEHCIOtherTDs(s2)
{
    reveal global_non_scratchpad_vars_except_counters_are_unchanged();

    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s1);
    reveal WK_ValidObjs_ObjIDs();

    var result1 := WSM_MapStateToAbstractTDs_ForEEHCIOtherTDs(s1);
    var result2 := WSM_MapStateToAbstractTDs_ForEEHCIOtherTDs(s2);
    forall id | id in result1
        ensures result1[id] == result2[id]
    {
        assert result1[id].pid == result2[id].pid;

        Lemma_WSM_eEHCI_GetUSBTDRegVal_GivenIDOfEEHCIOtherTDs_ProveSameResultIfOnlyTempGVarsCountersRegsAndStacksAreChanged(s1, s2, id);
        assert result1[id].val == result2[id].val;
    }
}

lemma Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs_USBTDs(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)

    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)

    ensures WSM_MapStateToAbstractTDs_ForUSBTDs(s1) == WSM_MapStateToAbstractTDs_ForUSBTDs(s2)
{
    reveal global_non_scratchpad_vars_except_counters_are_unchanged();

    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s1);
    reveal WK_ValidObjs_ObjIDs();

    var result1 := WSM_MapStateToAbstractTDs_ForUSBTDs(s1);
    var result2 := WSM_MapStateToAbstractTDs_ForUSBTDs(s2);
    forall id | id in result1
        ensures result1[id] == result2[id]
    {
        assert result1[id].pid == result2[id].pid;

        Lemma_WSM_USBTD_CalcTDVal_ProveSameResultIfOnlyTempGVarsCountersRegsAndStacksAreChanged(s1, s2, id);
        assert result1[id].val == result2[id].val;
    }
}

lemma Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs_OtherTDs(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)

    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)

    ensures WSM_MapStateToAbstractTDs_ForOSTDs(s1) == WSM_MapStateToAbstractTDs_ForOSTDs(s2)
    ensures WSM_MapStateToAbstractTDs_ForEEHCIHCodedTDs(s1) == WSM_MapStateToAbstractTDs_ForEEHCIHCodedTDs(s2)
    ensures WSM_MapStateToAbstractTDs_ForUSBPDev(s1) == WSM_MapStateToAbstractTDs_ForUSBPDev(s2)
{
    reveal global_non_scratchpad_vars_except_counters_are_unchanged();

    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s1);
    reveal WK_ValidObjs_ObjIDs();
}

lemma Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs_FDs(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)

    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)

    ensures WSM_MapState_GatherAllAbstractFDs(s1) == WSM_MapState_GatherAllAbstractFDs(s2)
{
    reveal global_non_scratchpad_vars_except_counters_are_unchanged();

    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s1);
    reveal WK_ValidObjs_ObjIDs();

    // Apply axioms
    forall id | id in s1.objects.usbtd_fds
        ensures WSM_USBTD_GetAbstractFDVal(s1, id) == WSM_USBTD_GetAbstractFDVal(s2, id)
    {
        Lemma_WSM_USBTD_GetAbstractFDVal_Property(s1, s2, id);
    }

    forall id | id in s1.objects.eehci_fds
        ensures WSM_eEHCI_GetAbstractFDVal(s1, id) == WSM_eEHCI_GetAbstractFDVal(s2, id)
    {
        Lemma_WSM_eEHCI_GetAbstractFDVal_Property(s1, s2, id);
    }
}

lemma Lemma_WKAPI_ChangeTempGVars_MapToSameDMState_Objs_DOs(s1:state, s2:state)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)

    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)

    ensures WSM_MapState_GatherAllAbstractDOs(s1) == WSM_MapState_GatherAllAbstractDOs(s2)
{
    reveal global_non_scratchpad_vars_except_counters_are_unchanged();

    Lemma_OpsSaneStateSubset_ProveWK_ValidObjs_ObjIDs(s1);
    reveal WK_ValidObjs_ObjIDs();

    // Apply axioms
    forall id | id in s1.objects.usbtd_dos
        ensures WSM_USBTD_GetAbstractDOVal(s1, id) == WSM_USBTD_GetAbstractDOVal(s2, id)
    {
        Lemma_WSM_USBTD_GetAbstractDOVal_Property(s1, s2, id);
    }

    forall id | id in s1.objects.eehci_dos
        ensures WSM_eEHCI_GetAbstractDOVal(s1, id) == WSM_eEHCI_GetAbstractDOVal(s2, id)
    {
        Lemma_WSM_eEHCI_GetAbstractDOVal_Property(s1, s2, id);
    }
}