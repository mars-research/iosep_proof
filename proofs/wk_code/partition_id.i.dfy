include "partition_id.s.dfy"


/*********************** Lemmas of pids_parse_g_wimp_pids ********************/
// Lemma: <pids_parse_g_wimp_pids> output results correctly 
lemma Lemma_pids_parse_g_existing_pids_CorrectOutput(globals:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals)
    ensures var existing:seq<word> := global_read_fullval(globals, G_Existing_PIDs());
            forall pid:WS_PartitionID :: pid in pids_parse_g_wimp_pids(globals)
                <==> (pid.v in existing && pid != WS_PartitionID(PID_INVALID))
        // Property: Correct conversion
{
    var existing:seq<word> := global_read_fullval(globals, G_Existing_PIDs());
    var ret_set := pids_parse_g_wimp_pids(globals);
    forall pid:WS_PartitionID | pid.v in existing && pid != WS_PartitionID(PID_INVALID)
        ensures pid in ret_set
    {
        if(pid !in ret_set)
        {
            assert pid.v !in existing || pid.v == PID_INVALID;
        }
    }
}

// Lemma: When replacing PIDs, <pids_parse_g_wimp_pids> of the <old_globals> and <new_globals> relates each other correctly
lemma Lemma_pids_parse_g_wimp_pids_CorrectnessOfSetChange(old_globals:globalsmap, new_globals:globalsmap, pid_vaddr:vaddr, old_pid:word, new_pid:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires is_valid_vaddr(pid_vaddr)
    requires is_gvar_valid_vaddr(G_Existing_PIDs(), pid_vaddr)
    requires !pids_is_os_pid(new_pid)
        // Requirement: <new_pid> must not be the OS partition's PID
    requires forall pid:WS_PartitionID :: pid in pids_parse_g_wimp_pids(old_globals)
            ==> (pid.v != new_pid)
        // Requirement: <new_pid> is new

    requires old_pid == global_read_word(old_globals, G_Existing_PIDs(), pid_vaddr)
    requires new_globals == global_write_word(old_globals, G_Existing_PIDs(), pid_vaddr, new_pid)

    ensures new_pid != PID_INVALID 
                ==> pids_parse_g_wimp_pids(new_globals) == pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)} + {WS_PartitionID(new_pid)}
    ensures new_pid == PID_INVALID 
                ==> pids_parse_g_wimp_pids(new_globals) == pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)}
{
    Lemma_pids_parse_g_existing_pids_CorrectOutput(old_globals);
    Lemma_pids_parse_g_existing_pids_CorrectOutput(new_globals);

    var old_existing := global_read_fullval(old_globals, G_Existing_PIDs());
    var new_existing := global_read_fullval(new_globals, G_Existing_PIDs());

    forall pid | pid in pids_parse_g_wimp_pids(new_globals)
        ensures pid in (pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)} + {WS_PartitionID(new_pid)})
    {
        assert pid.v in new_existing;
        assert pid.v != PID_INVALID;

        assert pid in (pids_parse_g_wimp_pids(old_globals) + {WS_PartitionID(new_pid)});


        if(new_pid == old_pid)
        {
            assert pid in (pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)} + {WS_PartitionID(new_pid)});
        }
        else
        {
            // Prove pid != WS_PartitionID(old_pid)
            if(pid.v == old_pid)
            {
                if(pid.v == new_pid)
                {
                    assert false;
                }
                else
                {
                    Lemma_pids_parse_g_wimp_pids_IfNewPIDIsDiffFromOverwrittenOldPID_ThenAllResultPIDsAreDiffFromOverwrittenOlDPID(
                        old_globals, new_globals, pid_vaddr, old_pid, new_pid);
                    assert false;
                }
            }
            assert pid != WS_PartitionID(old_pid);

            assert pid in (pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)} + {WS_PartitionID(new_pid)});
        }
    }

    if(new_pid != PID_INVALID)
    {
        forall pid | pid in (pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)} + {WS_PartitionID(new_pid)})
            ensures pid in pids_parse_g_wimp_pids(new_globals)
        {
            if(pid in (pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)}))
            {
                var old_j :| 0 <= old_j < |old_existing| && old_existing[old_j] == pid.v;
                assert new_existing[old_j] == pid.v;

                assert pid in pids_parse_g_wimp_pids(new_globals);
            }
            if(pid == WS_PartitionID(new_pid))
            {
                assert pid.v == new_pid;

                assert new_globals == global_write_word(old_globals, G_Existing_PIDs(), pid_vaddr, new_pid);
                var new_i := BytesToWords(pid_vaddr - AddressOfGlobal(G_Existing_PIDs()));
                assert new_existing[new_i] == new_pid;
                
                assert pid in pids_parse_g_wimp_pids(new_globals);
            }
        }
    }
    else
    {
        forall pid | pid in (pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)})
            ensures pid in pids_parse_g_wimp_pids(new_globals)
        {
            if(pid in (pids_parse_g_wimp_pids(old_globals) - {WS_PartitionID(old_pid)}))
            {
                var old_j :| 0 <= old_j < |old_existing| && old_existing[old_j] == pid.v;
                assert new_existing[old_j] == pid.v;

                assert pid in pids_parse_g_wimp_pids(new_globals);
            }
        }
    }
}




/*********************** Lemmas of pids_parse_g_wimp_pids ********************/
// Lemma: If globals1 == globals2, and WK_ValidPartitionIDs_InGlobalVars(globals1),
// Then WK_ValidPartitionIDs_InGlobalVars(globals2)
lemma Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGVarUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires globals1 == globals2
    requires WK_ValidPartitionIDs_InGlobalVars(globals1)

    ensures WK_ValidPartitionIDs_InGlobalVars(globals2)
{
    Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGVarUnchanged(globals1, globals2);
    Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGVarUnchanged(globals1, globals2);
}

// Lemma: If gvar_read_fullval(globals1, G_Existing_PIDs()) == gvar_read_fullval(globals2, G_Existing_PIDs()), and 
// WK_ValidPartitionIDs_InGlobalVars(globals1),
// Then WK_ValidPartitionIDs_InGlobalVars(globals2)
lemma Lemma_WK_ValidPartitionIDs_InGlobalVars_PreserveInNewState_IfGExistingPIDsAndPIDCounterUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs())
    requires global_read_fullval(globals1, G_PID_Counter()) == global_read_fullval(globals2, G_PID_Counter())
    requires WK_ValidPartitionIDs_InGlobalVars(globals1)

    ensures WK_ValidPartitionIDs_InGlobalVars(globals2)
{
    Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(globals1, globals2);
    Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(globals1, globals2);
}



// Lemma: When writting <new_pid> into <old_globals> which satisfies pids_g_existing_pids_no_duplicate, if <new_pid>
// is different from existing values in pids_parse_g_wimp_pids(old_globals), then the result global variable
// after writting must satisfy pids_g_existing_pids_no_duplicate
lemma Lemma_pids_g_existing_pids_no_duplicate_HoldAfterWritingNonDuplicateValue(old_globals:globalsmap, new_globals:globalsmap, vaddr:vaddr, new_pid:word)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires is_gvar_valid_vaddr(G_Existing_PIDs(), vaddr)
    
    requires pids_g_existing_pids_no_duplicate(old_globals)
            // Requirement 1: <old_globals> satisfies <pids_g_existing_pids_no_duplicate>
    requires new_globals == global_write_word(old_globals, G_Existing_PIDs(), vaddr, new_pid)
    requires forall pid:WS_PartitionID :: pid in pids_parse_g_wimp_pids(old_globals)
            ==> (pid.v != new_pid)
            // Requirement 2: <new_pid> does not appear in pids_parse_g_wimp_pids(old_globals)

    ensures pids_g_existing_pids_no_duplicate(new_globals)
{
    var old_existing:seq<word> := global_read_fullval(new_globals, G_Existing_PIDs());
    var existing:seq<word> := global_read_fullval(new_globals, G_Existing_PIDs());

    var idx := BytesToWords(vaddr - AddressOfGlobal(G_Existing_PIDs()));
    assert existing == old_existing[idx := new_pid];

    forall i, j | (0 <= i < |existing| && 0 <= j < |existing|) &&
            (existing[i] != PID_INVALID && existing[j] != PID_INVALID)
                // If two PIDs are not PID_INVALID
        ensures (existing[i] == existing[j] ==> i == j)
    {
        if(i != idx && j != idx)
        {
            assert existing[i] == old_existing[i];
            assert existing[j] == old_existing[j];

            Lemma_pids_g_existing_pids_no_duplicate_Apply(old_globals, i, j);
            assert (old_existing[i] == old_existing[j] <==> i == j);
            assert (existing[i] == existing[j] ==> i == j);
        }

        Lemma_pids_parse_g_existing_pids_CorrectOutput(old_globals);
        if(i == idx && j != idx)
        {
            assert existing[i] == new_pid;

            assert WS_PartitionID(existing[j]) in pids_parse_g_wimp_pids(old_globals);
            assert existing[j] != new_pid;
            assert (existing[i] == existing[j] ==> i == j);
        }

        if(i != idx && j == idx)
        {
            assert existing[j] == new_pid;

            assert WS_PartitionID(existing[i]) in pids_parse_g_wimp_pids(old_globals);
            assert existing[i] != new_pid;
            assert (existing[i] == existing[j] ==> i == j);
        }
    }
}




/*********************** Private Lemmas of pids_parse_g_wimp_pids ********************/
// Lemma: For pids_parse_g_wimp_pids, if an old PID is overwritten, then all result PIDs are different from the old PID
lemma Lemma_pids_parse_g_wimp_pids_IfNewPIDIsDiffFromOverwrittenOldPID_ThenAllResultPIDsAreDiffFromOverwrittenOlDPID(
    old_globals:globalsmap, new_globals:globalsmap, pid_vaddr:vaddr, old_pid:word, new_pid:word
)
    requires WK_ValidGlobalVars_Decls(old_globals)
    requires WK_ValidGlobalVars_Decls(new_globals)
    requires pids_g_existing_pids_no_duplicate(old_globals)

    requires is_valid_vaddr(pid_vaddr)
    requires is_gvar_valid_vaddr(G_Existing_PIDs(), pid_vaddr)
    requires !pids_is_os_pid(new_pid)
        // Requirement: <new_pid> must not be the OS partition's PID
    requires forall pid:WS_PartitionID :: pid in pids_parse_g_wimp_pids(old_globals)
            ==> (pid.v != new_pid)
        // Requirement: <new_pid> is new

    requires old_pid == global_read_word(old_globals, G_Existing_PIDs(), pid_vaddr)
    requires new_globals == global_write_word(old_globals, G_Existing_PIDs(), pid_vaddr, new_pid)

    ensures forall pid :: pid in pids_parse_g_wimp_pids(new_globals)
            ==> pid != WS_PartitionID(old_pid)
{
    var old_existing := global_read_fullval(old_globals, G_Existing_PIDs());
    var new_existing := global_read_fullval(new_globals, G_Existing_PIDs());

    Lemma_pids_g_existing_pids_no_duplicate_HoldAfterWritingNonDuplicateValue(old_globals, new_globals, pid_vaddr, new_pid);

    forall pid:WS_PartitionID | pid in pids_parse_g_wimp_pids(new_globals)
        ensures pid != WS_PartitionID(old_pid)
    {
        if(pid.v != new_pid)
        {
            assert pid in pids_parse_g_wimp_pids(old_globals);
            assert pid in pids_parse_g_wimp_pids(new_globals);

            if (pid == WS_PartitionID(old_pid))
            {
                var new_j :| 0 <= new_j < |new_existing| && new_existing[new_j] == old_pid;
                var old_i := BytesToWords(pid_vaddr - AddressOfGlobal(G_Existing_PIDs()));
                assert old_existing[new_j] == old_pid;
                assert old_existing[old_i] == old_pid;
                assert new_j != old_i;


                assert old_pid != PID_INVALID;
                assert !pids_g_existing_pids_no_duplicate(old_globals);

                assert false;
            }

            assert pid != WS_PartitionID(old_pid);
        }
        else
        {
            assert pid != WS_PartitionID(old_pid);
        }
    }
}




/*********************** Private Lemmas ********************/
// Lemma: If globals1 == globals2, and pids_g_existing_pids_no_duplicate(globals1),
// Then pids_g_existing_pids_no_duplicate(globals2)
lemma Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGVarUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires globals1 == globals2
    requires pids_g_existing_pids_no_duplicate(globals1)

    ensures pids_g_existing_pids_no_duplicate(globals2)
{
    var existing1:seq<word> := global_read_fullval(globals1, G_Existing_PIDs());
    var existing2:seq<word> := global_read_fullval(globals2, G_Existing_PIDs());

    assert existing1 == existing2;
}

// Lemma: If globals1 == globals2, and pids_g_existing_pids_exclude_os_pid(globals1),
// Then pids_g_existing_pids_exclude_os_pid(globals2)
lemma Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGVarUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires globals1 == globals2
    requires pids_g_existing_pids_exclude_os_pid(globals1)

    ensures pids_g_existing_pids_exclude_os_pid(globals2)
{
    var existing1:seq<word> := global_read_fullval(globals1, G_Existing_PIDs());
    var existing2:seq<word> := global_read_fullval(globals2, G_Existing_PIDs());

    assert existing1 == existing2;
}

// Lemma: If gvar_read_fullval(globals1, G_Existing_PIDs()) == gvar_read_fullval(globals2, G_Existing_PIDs()), and 
// pids_g_existing_pids_no_duplicate(globals1),
// Then pids_g_existing_pids_no_duplicate(globals2)
lemma Lemma_pids_g_existing_pids_no_duplicate_PreserveInNewState_IfGExistingPIDsUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs())
    requires pids_g_existing_pids_no_duplicate(globals1)

    ensures pids_g_existing_pids_no_duplicate(globals2)
{
    var existing1:seq<word> := global_read_fullval(globals1, G_Existing_PIDs());
    var existing2:seq<word> := global_read_fullval(globals2, G_Existing_PIDs());

    assert existing1 == existing2;
}

// Lemma: If gvar_read_fullval(globals1, G_Existing_PIDs()) == gvar_read_fullval(globals2, G_Existing_PIDs()), and 
// pids_g_existing_pids_exclude_os_pid(globals1),
// Then pids_g_existing_pids_exclude_os_pid(globals2)
lemma Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfGExistingPIDsUnchanged(globals1:globalsmap, globals2:globalsmap)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires global_read_fullval(globals1, G_Existing_PIDs()) == global_read_fullval(globals2, G_Existing_PIDs())
    requires pids_g_existing_pids_exclude_os_pid(globals1)

    ensures pids_g_existing_pids_exclude_os_pid(globals2)
{
    var existing1:seq<word> := global_read_fullval(globals1, G_Existing_PIDs());
    var existing2:seq<word> := global_read_fullval(globals2, G_Existing_PIDs());

    assert existing1 == existing2;
}

lemma Lemma_pids_g_existing_pids_no_duplicate_Apply(globals:globalsmap, i:int, j:int)
    requires WK_ValidGlobalVars_Decls(globals)
    requires pids_g_existing_pids_no_duplicate(globals)

    requires var existing:seq<word> := global_read_fullval(globals, G_Existing_PIDs());
            (0 <= i < |existing| && 0 <= j < |existing|) &&
            (existing[i] != PID_INVALID && existing[j] != PID_INVALID)

    ensures var existing:seq<word> := global_read_fullval(globals, G_Existing_PIDs());
            (existing[i] == existing[j] <==> i == j)
{
    // Dafny can automatically prove this lemma
}

// Lemma: If the new PID does not fulfill <pids_is_os_pid>, and pids_g_existing_pids_exclude_os_pid(globals1),
// Then pids_g_existing_pids_exclude_os_pid(globals2)
lemma Lemma_pids_g_existing_pids_exclude_os_pid_PreserveInNewState_IfNotWritingInOSPID(globals1:globalsmap, globals2:globalsmap, pid_vaddr:vaddr, new_pid:word)
    requires WK_ValidGlobalVars_Decls(globals1)
    requires WK_ValidGlobalVars_Decls(globals2)
    requires pids_g_existing_pids_exclude_os_pid(globals1)

    requires is_valid_vaddr(pid_vaddr)
    requires is_gvar_valid_vaddr(G_Existing_PIDs(), pid_vaddr)
    requires !pids_is_os_pid(new_pid)
        // Requirement: <new_pid> must not be the OS partition's PID

    requires globals2 == global_write_word(globals1, G_Existing_PIDs(), pid_vaddr, new_pid)

    ensures pids_g_existing_pids_exclude_os_pid(globals2)
{
    var existing1:seq<word> := global_read_fullval(globals1, G_Existing_PIDs());
    var existing2:seq<word> := global_read_fullval(globals2, G_Existing_PIDs());

    // Prove no elements in <existing1> is PID_RESERVED_OS_PARTITION
    forall i | 0 <= i < |existing1|
        ensures existing1[i] != PID_RESERVED_OS_PARTITION
    {
        assert existing1[i] in existing1;
    }

    forall i | 0 <= i < |existing2|
        ensures existing2[i] != PID_RESERVED_OS_PARTITION
    {
        if(existing2[i] == PID_RESERVED_OS_PARTITION)
        {
            if(i * WK_Existing_PID_ENTRY_SZ + G_Existing_PIDs_Entry_PID_BytesOffset != pid_vaddr)
            {
                assert existing2[i] == existing1[i];
                assert false;
            }
            assert i * WK_Existing_PID_ENTRY_SZ + G_Existing_PIDs_Entry_PID_BytesOffset == pid_vaddr;

            assert false;
        }
    }
}