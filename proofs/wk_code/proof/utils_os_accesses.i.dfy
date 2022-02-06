include "utils_os_accesses.s.dfy"
include "DM_AdditionalPropertiesLemmas.i.dfy"

lemma Lemma_WSM_DevRead_TransfersMustBeDefinedInWSDesignModel_ImpliesDM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(
    s:state, dm:DM_State, dev_sid:Subject_ID,
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active

    requires WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, read_tds, read_fds, read_dos)

    ensures var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
            DM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers(dm, dev_sid, read_objs)
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);

    assert DM_DevRead_TransfersMustBeDefinedInWSDesignModel(dm, dev_sid, read_tds, read_fds, read_dos);

    var read_objs := TDIDsToObjIDs(read_tds) + FDIDsToObjIDs(read_fds) + DOIDsToObjIDs(read_dos);
    var k := DMStateToState(dm);

    forall o_id | o_id in read_objs
        ensures R in DevAModesToObj(k, ActiveTDsState(k), Dev_ID(dev_sid), o_id)
    {
        var k_tds_state := ActiveTDsState(k);
        var dev_id := Dev_ID(dev_sid);

        assert TD_ID(o_id) in read_tds || FD_ID(o_id) in read_fds || DO_ID(o_id) in read_dos;

        Lemma_DMStateToState_SecureK(dm, k);
        if(TD_ID(o_id) in read_tds)
        {
            assert K_DevRead_ReadTDMustBeInATransfer(k, dev_sid, TD_ID(o_id));
            Lemma_WSM_DevRead_TransfersMustBeDefinedInWSDesignModel_ImpliesDM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers_TD(
                s, dm, dev_sid, read_tds, read_fds, read_dos, o_id);
            assert R in DevAModesToObj(k, k_tds_state, dev_id, o_id);
        }
        else if(FD_ID(o_id) in read_fds)
        {
            assert K_DevRead_ReadFDMustBeInATransfer(k, dev_sid, FD_ID(o_id));
            Lemma_WSM_DevRead_TransfersMustBeDefinedInWSDesignModel_ImpliesDM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers_FD(
                s, dm, dev_sid, read_tds, read_fds, read_dos, o_id);
            assert R in DevAModesToObj(k, k_tds_state, dev_id, o_id);
        }
        else
        {
            assert DO_ID(o_id) in read_dos;

            assert K_DevRead_ReadDOMustBeInATransfer(k, dev_sid, DO_ID(o_id));
            Lemma_WSM_DevRead_TransfersMustBeDefinedInWSDesignModel_ImpliesDM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers_DO(
                s, dm, dev_sid, read_tds, read_fds, read_dos, o_id);
            assert R in DevAModesToObj(k, k_tds_state, dev_id, o_id);
        }
    }
}




/*********************** Private Lemmas ********************/
lemma Lemma_WSM_DevRead_TransfersMustBeDefinedInWSDesignModel_ImpliesDM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers_TD(
    s:state, dm:DM_State, dev_sid:Subject_ID,
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>,
    o_id:Object_ID
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active

    requires WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, read_tds, read_fds, read_dos)

    requires TD_ID(o_id) in read_tds

    ensures var k := DMStateToState(dm);
            SubjPID(k, dev_sid) != NULL
    ensures var k := DMStateToState(dm);
            var k_tds_state := ActiveTDsState(k);
            var dev_id := Dev_ID(dev_sid);
            R in DevAModesToObj(k, k_tds_state, dev_id, o_id);
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);
    var k := DMStateToState(dm);

    // Prove SubjPID(k, dev_sid) != NULL
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    assert SubjPID(k, dev_sid) != NULL;

    // Apply WSM_DevRead_TransfersMustBeDefinedInWSDesignModel
    assert DM_DevRead_TransfersMustBeDefinedInWSDesignModel(dm, dev_sid, read_tds, read_fds, read_dos);

    var k_tds_state := ActiveTDsState(k);
    var dev_id := Dev_ID(dev_sid);

    Lemma_DMStateToState_SecureK(dm, k);
    assert IsValidState(k) && IsSecureState(k);
    assert K_DevRead_ReadTDMustBeInATransfer(k, dev_sid, TD_ID(o_id));
    Lemma_K_DevRead_ReadTDMustBeInATransfer_ProveReadInDevAModesToObj(k, dev_sid, TD_ID(o_id));
    assert R in DevAModesToObj(k, k_tds_state, dev_id, o_id);
}

lemma Lemma_WSM_DevRead_TransfersMustBeDefinedInWSDesignModel_ImpliesDM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers_FD(
    s:state, dm:DM_State, dev_sid:Subject_ID,
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>,
    o_id:Object_ID
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active

    requires WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, read_tds, read_fds, read_dos)

    requires FD_ID(o_id) in read_fds

    ensures var k := DMStateToState(dm);
            SubjPID(k, dev_sid) != NULL
    ensures var k := DMStateToState(dm);
            var k_tds_state := ActiveTDsState(k);
            var dev_id := Dev_ID(dev_sid);
            R in DevAModesToObj(k, k_tds_state, dev_id, o_id);
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);
    var k := DMStateToState(dm);

    // Prove SubjPID(k, dev_sid) != NULL
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    assert SubjPID(k, dev_sid) != NULL;

    // Apply WSM_DevRead_TransfersMustBeDefinedInWSDesignModel
    assert DM_DevRead_TransfersMustBeDefinedInWSDesignModel(dm, dev_sid, read_tds, read_fds, read_dos);

    var k_tds_state := ActiveTDsState(k);
    var dev_id := Dev_ID(dev_sid);

    Lemma_DMStateToState_SecureK(dm, k);
    assert IsValidState(k) && IsSecureState(k);
    assert K_DevRead_ReadFDMustBeInATransfer(k, dev_sid, FD_ID(o_id));
    Lemma_K_DevRead_ReadFDMustBeInATransfer_ProveReadInDevAModesToObj(k, dev_sid, FD_ID(o_id));
    assert R in DevAModesToObj(k, k_tds_state, dev_id, o_id);
}

lemma Lemma_WSM_DevRead_TransfersMustBeDefinedInWSDesignModel_ImpliesDM_DevRead_ReadSrcObjsToDestObjs_ReadMustFromCorrespondingTransfers_DO(
    s:state, dm:DM_State, dev_sid:Subject_ID,
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>,
    o_id:Object_ID
)
    requires OpsSaneState(s)
    requires dm == WSM_MapSecureState(s)

    requires WSM_IsDevID(s.subjects, Dev_ID(dev_sid))
    requires WSM_SubjPID(s.subjects, s.objects, s.id_mappings, wkm_get_globals(s.wk_mstate), dev_sid) 
                != WS_PartitionID(PID_INVALID)
        // Requirement: the device must be active

    requires WSM_DevRead_TransfersMustBeDefinedInWSDesignModel(s, dev_sid, read_tds, read_fds, read_dos)

    requires DO_ID(o_id) in read_dos

    ensures var k := DMStateToState(dm);
            SubjPID(k, dev_sid) != NULL
    ensures var k := DMStateToState(dm);
            var k_tds_state := ActiveTDsState(k);
            var dev_id := Dev_ID(dev_sid);
            R in DevAModesToObj(k, k_tds_state, dev_id, o_id);
{
    var dm:DM_State := WSM_MapState(s);
    Lemma_SaneWSMState_MapToSecureDMState(s, dm);
    assert DM_IsValidState(dm) && DM_IsSecureState(dm);
    var k := DMStateToState(dm);

    // Prove SubjPID(k, dev_sid) != NULL
    Lemma_WSMStateMapping_EquivilantSubjIDsAndPIDs(s, dm);
    assert SubjPID(k, dev_sid) != NULL;

    // Apply WSM_DevRead_TransfersMustBeDefinedInWSDesignModel
    assert DM_DevRead_TransfersMustBeDefinedInWSDesignModel(dm, dev_sid, read_tds, read_fds, read_dos);

    var k_tds_state := ActiveTDsState(k);
    var dev_id := Dev_ID(dev_sid);

    Lemma_DMStateToState_SecureK(dm, k);
    assert IsValidState(k) && IsSecureState(k);
    assert K_DevRead_ReadDOMustBeInATransfer(k, dev_sid, DO_ID(o_id));
    Lemma_K_DevRead_ReadDOMustBeInATransfer_ProveReadInDevAModesToObj(k, dev_sid, DO_ID(o_id));
    assert R in DevAModesToObj(k, k_tds_state, dev_id, o_id);
}