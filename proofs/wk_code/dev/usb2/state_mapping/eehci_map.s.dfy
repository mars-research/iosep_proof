include "../../../state_properties_OpsSaneStateSubset.s.dfy"
include "../../../utils/model/utils_objaddrs.s.dfy"
include "../../../drv/drv.i.dfy"
include "../usb_tds_ops/secure_usbtd.i.dfy"
include "../public/usb_lemmas.i.dfy"

/*********************** Axioms ********************/
// [State/Ops Mapping] Axiom (well known): The returned value corresponds to the FD's content in the eEHCI's memory/register
// [NOTE] This function should calculate the eEHCI owning the object
function {:axiom} WSM_eEHCI_GetAbstractFDVal(s:state, fd_id:FD_ID) : (result:FD_Val)
    requires fd_id in s.objects.eehci_fds

// [State/Ops Mapping] Axiom (well known): If only temp global variables, counters, registers, and stack are changed, this 
// function returns the same result
// [NOTE] Different counter values do not impact the mappings. This is because counters are not mapped to state variables
// in WK design. Counters are used in SIs instead.
lemma {:axiom} Lemma_WSM_eEHCI_GetAbstractFDVal_Property(s1:state, s2:state, fd_id:FD_ID)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)
    requires fd_id in s1.objects.eehci_fds
    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)
    ensures WSM_eEHCI_GetAbstractFDVal(s1, fd_id) == WSM_eEHCI_GetAbstractFDVal(s2, fd_id)

// [State/Ops Mapping] Axiom (well known): The returned value corresponds to the DO's content in the eEHCI's memory/register
// [NOTE] This function should calculate the eEHCI owning the object
function {:axiom} WSM_eEHCI_GetAbstractDOVal(s:state, do_id:DO_ID) : (result:DO_Val)
    requires do_id in s.objects.eehci_dos

// [State/Ops Mapping] Axiom (well known): If only temp global variables, counters, registers, and stack are changed, this 
// function returns the same result
// [NOTE] Different counter values do not impact the mappings. This is because counters are not mapped to state variables
// in WK design. Counters are used in SIs instead.
lemma {:axiom} Lemma_WSM_eEHCI_GetAbstractDOVal_Property(s1:state, s2:state, do_id:DO_ID)
    requires OpsSaneStateSubset(s1)
    requires OpsSaneStateSubset(s2)
    requires do_id in s1.objects.eehci_dos
    requires state_equal_except_tempgvar_regs_stack_counters(s1, s2)
    ensures WSM_eEHCI_GetAbstractDOVal(s1, do_id) == WSM_eEHCI_GetAbstractDOVal(s2, do_id)