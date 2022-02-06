include "eehci.s.dfy"
include "../../state_properties_validity.s.dfy"

/*********************** Axioms ********************/
// [HW] Axiom (well known): EEHCIs do not define write transfers to any TDs
lemma {:axiom} Lemma_EEHCI_HCodedTDDoNotDefineWriteTransferToTDs(s:state, eehci_id:Dev_ID)
    requires ValidState(s)
    requires eehci_id in s.subjects.eehcis

    requires s.subjects.eehcis[eehci_id].hcoded_td_id in s.objects.eehci_hcoded_tds
        // Properties needed by the following properties
    ensures forall hcoded_td_id, td_id :: hcoded_td_id == s.subjects.eehcis[eehci_id].hcoded_td_id &&
                    td_id in s.objects.eehci_hcoded_tds[hcoded_td_id].trans_params_tds
                ==> W !in s.objects.eehci_hcoded_tds[hcoded_td_id].trans_params_tds[td_id].amodes