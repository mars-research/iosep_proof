include "utils_subjs_any_state.s.dfy"

lemma Lemma_WSM_AllDevIDs_pEHCIs_ProveEqual(s:state, s':state)
    requires forall dev_id :: dev_id in s.activate_conds.ehci_activate_cond
                ==> dev_id in s.subjects.os_devs
        // Requirement from <WK_ValidState_DevsActivateCond>
    requires MapGetKeys(s.subjects.os_drvs) == MapGetKeys(s'.subjects.os_drvs)
    requires MapGetKeys(s.subjects.os_devs) == MapGetKeys(s'.subjects.os_devs)
    requires MapGetKeys(s.subjects.wimp_drvs) == MapGetKeys(s'.subjects.wimp_drvs)
    requires MapGetKeys(s.subjects.eehcis) == MapGetKeys(s'.subjects.eehcis)
    requires MapGetKeys(s.subjects.usbpdevs) == MapGetKeys(s'.subjects.usbpdevs)

    requires s.activate_conds == s'.activate_conds

    ensures WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds) == WSM_AllDevIDs_pEHCIs(s'.subjects, s'.activate_conds)
{
    forall dev_id | dev_id in s'.activate_conds.ehci_activate_cond
        ensures dev_id in s'.subjects.os_devs
    {
        assert dev_id in s.activate_conds.ehci_activate_cond;
        assert dev_id in s.subjects.os_devs;

        assert MapGetKeys(s.subjects.os_devs) == MapGetKeys(s'.subjects.os_devs);
        Lemma_MapSameKeys(s.subjects.os_devs, s'.subjects.os_devs);
    }

    assert WSM_AllDevIDs_pEHCIs(s.subjects, s.activate_conds) == MapGetKeys(s.activate_conds.ehci_activate_cond);
    assert WSM_AllDevIDs_pEHCIs(s'.subjects, s'.activate_conds) == MapGetKeys(s'.activate_conds.ehci_activate_cond);
}