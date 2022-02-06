include "../../WK_Design/Model.dfy"

// Predicate: If the OS device reads a set of TDs/FDs/DOs , then the device must be able to read the corresponding 
// objects in the WK design model
predicate DM_DevRead_TransfersMustBeDefinedInWSDesignModel(
    dm:DM_State, dev_sid:Subject_ID, 
    read_tds:set<TD_ID>, read_fds:set<FD_ID>, read_dos:set<DO_ID>
)
    requires DM_IsValidState(dm) && DM_IsSecureState(dm)
    requires DM_IsDevID(dm.subjects, Dev_ID(dev_sid))
    requires DM_SubjPID(dm.subjects, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    var k := DMStateToState(dm);
    Lemma_DMStateToState_SecureK(dm, k);
    assert IsValidState(k) && IsSecureState(k);
    Lemma_ValidDMState_SameSubjIDsPIDsBetweenWKAndK(dm, k);

    (forall id :: id in read_tds
            ==> K_DevRead_ReadTDMustBeInATransfer(k, dev_sid, id)) &&
        // Requirement: The device (<Dev_ID(dev_sid)>) must have transfers to
        // the objects
    (forall id :: id in read_fds
            ==> K_DevRead_ReadFDMustBeInATransfer(k, dev_sid, id)) &&
        // Requirement: The device (<Dev_ID(dev_sid)>) must have transfers to
        // the objects
    (forall id :: id in read_dos
            ==> K_DevRead_ReadDOMustBeInATransfer(k, dev_sid, id)) &&
        // Requirement: The device (<Dev_ID(dev_sid)>) must have transfers to
        // the objects
    (true)
}

// Predicate: For all transfers defined in <val>, the target objects must have different object IDs
// [TOOD] This predicate should be proven as a corollary in the I/O separation model
predicate K_DevRead_TDRefObjWithDifferentObjectID(val:TD_Val)
{
    (forall id1, id2 :: id1 in val.trans_params_tds && id2 in val.trans_params_fds
        ==> id1.oid != id2.oid
    ) &&
    (forall id1, id2 :: id1 in val.trans_params_tds && id2 in val.trans_params_dos
        ==> id1.oid != id2.oid
    ) &&
    (forall id1, id2 :: id1 in val.trans_params_fds && id2 in val.trans_params_dos
        ==> id1.oid != id2.oid
    )
}

predicate K_DevRead_ReadTDMustBeInATransfer(
    k:State, dev_sid:Subject_ID, target_td_id:TD_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_td_id in GetTDVal(k, td_id).trans_params_tds &&
                    R in GetTDVal(k, td_id).trans_params_tds[target_td_id].amodes &&
                        // The TD references the target TD (<target_td_id>) with R
                    K_DevRead_TDRefObjWithDifferentObjectID(GetTDVal(k, td_id))
                        // [TOOD] This predicate should be proven as a corollary in the I/O separation model, instead of
                        // a pre-condition of DevRead
    )
        // For the read to the TD (<target_td_id>), it must be from an active TD (<td_id>) that can be 
        // read by the active device (<Dev_ID(dev_sid)>)
}

predicate K_DevRead_ReadFDMustBeInATransfer(
    k:State, dev_sid:Subject_ID, target_fd_id:FD_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_fd_id in GetTDVal(k, td_id).trans_params_fds &&
                    R in GetTDVal(k, td_id).trans_params_fds[target_fd_id].amodes &&
                        // The TD references the target FD (<target_fd_id>) with R
                    K_DevRead_TDRefObjWithDifferentObjectID(GetTDVal(k, td_id))
                        // [TOOD] This predicate should be proven as a corollary in the I/O separation model, instead of
                        // a pre-condition of DevRead
    )
        // For the read to the FD (<target_fd_id>), it must be from an active TD (<td_id>) that can be 
        // read by the active device (<Dev_ID(dev_sid)>)
}

predicate K_DevRead_ReadDOMustBeInATransfer(
    k:State, dev_sid:Subject_ID, target_do_id:DO_ID
)
    requires IsValidState(k) && IsSecureState(k)
    requires Dev_ID(dev_sid) in k.subjects.devs
    requires SubjPID(k, dev_sid) != NULL
        // Requirement: The driver is in the state and is active
{
    (exists td_id :: td_id in AllTDIDs(k.objects) &&
                    ObjPID(k, td_id.oid) != NULL &&
                        // Exists an active TD (<td_id>) in the state 
                    CanActiveDevReadActiveTD(KToKParams(k), 
                        ActiveTDsState(k), Dev_ID(dev_sid), td_id) &&
                        // The device can read the active TD
                    target_do_id in GetTDVal(k, td_id).trans_params_dos &&
                    R in GetTDVal(k, td_id).trans_params_dos[target_do_id].amodes &&
                        // The TD references the target DO (<target_do_id>) with R
                    K_DevRead_TDRefObjWithDifferentObjectID(GetTDVal(k, td_id))
                        // [TOOD] This predicate should be proven as a corollary in the I/O separation model, instead of
                        // a pre-condition of DevRead
    )
        // For the read to the DO (<target_do_id>), it must be from an active TD (<td_id>) that can be 
        // read by the active device (<Dev_ID(dev_sid)>)
}