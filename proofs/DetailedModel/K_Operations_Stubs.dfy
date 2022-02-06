include "../Abstract/Model.dfy"

// [TODO] This file is an ugly hack. It should be removed once we convert operations in the abstract model to be Dafny 
// functions
// [NOTE] Axioms in this file have already proved in the abstract model. 

function {:axiom} DrvWrite_Stub(
    k:State, 
    drv_sid:Subject_ID, // ID of the driver issues the write access
    td_id_val_map:map<TD_ID, TD_Val>, // IDs of TDs, and values to be written
    fd_id_val_map:map<FD_ID, FD_Val>, // IDs of FDs, and values to be written
    do_id_val_map:map<DO_ID, DO_Val> // IDs of DOs, and values to be written
) : (result:(State, bool)) //returns (k':State, d:bool)
    requires IsValidState(k) && IsSecureState(k)
    requires Drv_ID(drv_sid) in k.subjects.drvs
    requires IDToDrv(k, Drv_ID(drv_sid)).pid != NULL
        // Requirement: The driver is in the state and is active
    requires (forall td_id :: td_id in td_id_val_map ==> td_id in AllTDIDs(k.objects)) &&
             (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in AllFDIDs(k.objects)) &&
             (forall do_id :: do_id in do_id_val_map ==> do_id in AllDOIDs(k.objects))
    requires forall dev_id :: dev_id in k.subjects.devs
                ==> k.subjects.devs[dev_id].hcoded_td_id !in td_id_val_map
        // Requirement: The driver does not write any hardcoded TDs

    ensures var k' := result.0;
            var d := result.1;
            IsValidState(k') && IsSecureState(k')
    ensures var k' := result.0;
            var d := result.1;
            IsSecureOps(k, k')
    
    ensures var k' := result.0;
            var d := result.1;
            d == true ==> P_K_SubjWrite_ObjsToWriteMustBeInSamePartitionWithSubj(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
        // Property 3: All written objects are in the same partition with the driver
    ensures var k' := result.0;
            var d := result.1;
            P_OpsProperties_DrvWriteOp(k, DrvWriteOp(drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map))
        
    ensures var k' := result.0;
            var d := result.1;
            d == true <==> (
                    (forall td_id :: td_id in td_id_val_map ==> td_id in k.objects.active_non_hcoded_tds) &&
                    (forall fd_id :: fd_id in fd_id_val_map ==> fd_id in k.objects.active_fds) &&
                    (forall do_id :: do_id in do_id_val_map ==> do_id in k.objects.active_dos) &&
                    P_DrvWrite_ReturnTrue_Def(k, drv_sid, td_id_val_map, fd_id_val_map, do_id_val_map)
            )
    ensures var k' := result.0;
            var d := result.1;
            (d == true ==> P_DrvDevWrite_ModificationToState(k, td_id_val_map, fd_id_val_map, do_id_val_map, k'))
    ensures var k' := result.0;
            var d := result.1;
            d == false ==> k' == k