include "Utils.dfy"

function method DM_AllHCodedTDIDs(ws_subjects:Subjects) : set<TD_ID>
    ensures forall td_id :: td_id in DM_AllHCodedTDIDs(ws_subjects)
                <==> (exists dev_id :: dev_id in ws_subjects.devs &&
                      td_id == ws_subjects.devs[dev_id].hcoded_td_id)
{
    AllHCodedTDIDs(ws_subjects)
}