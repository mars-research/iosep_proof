include "../drv/drv.i.dfy"
include "../partition_id.i.dfy"
include "../drv/drv.ffi.s.dfy"
include "../state_properties_OpsSaneStateSubset.i.dfy"
include "../transition_constraints.s.dfy"
include "../proof/state_map_OpsSaneStateSubset.s.dfy"
include "../proof/state_map_OpsSaneStateSubset.i.dfy"
include "../proof/state_map_OpsSaneState.i.dfy"
include "../proof/io_accesses_ops_lemmas.i.dfy"
include "../proof/io_accesses.dfy"
include "../proof/utils_wimp_accesses.s.dfy"
include "../utils/model/utils_objs_valid_state.s.dfy"
include "../utils/model/headers_any_state.dfy"
include "../utils/model/utils_objaddrs.s.dfy"
include "../ins/x86/valesupp.i.dfy"
include "../state_properties_validity.i.dfy"
include "../dev/usb2/public/usb_lemmas.i.dfy"
include "../dev/usb2/usb_tds_utils.i.dfy"
include "../dev/usb2/usb_pdev_validstate.i.dfy"
include "../dev/usb2/state_mapping/eehci_map.s.dfy"
include "../dev/usb2/state_mapping/usbtd_map.s.dfy"
include "../dev/usb2/usb_tds_ops/secure_usbtd.i.dfy"
include "../dev/usb2/usb_tds_ops/usb_tds_ops.i.dfy"
include "../arch/common/arch_mem.i.dfy"
include "../utils/model/utils_subjs_objs.i.dfy"
include "../utils/model/utils_subjs_any_state.i.dfy"

include "../dev/usb2/eehci_ops.gen.dfy"
include "../dev/usb2/usb_tds_ops/usb_tds_ops.gen.dfy"
include "../dev/usb2/usb_pdev_utils.gen.dfy"
include "../dev/usb2/usb_tds_ops/usb_tds_ops.gen.dfy"
include "../mhv/mhv.ffi.i.dfy"

include "../proof/utils_os_accesses.i.dfy"
include "../proof/wkapi_commutative_diagram.i.dfy"
include "../proof/DM_Operations_Stubs.s.dfy"
include "../utils/model/utils_objs_secure_state.i.dfy"

include "../../DetailedModel/utils/Collections.dfy"
include "../../DetailedModel/Model.dfy"
include "../os/os_ops.gen.dfy"
include "../os/os_ops_impl.gen.dfy"
include "../wk_partition_ops.gen.dfy"
include "../SecurityProperties_Ops.dfy"
include "../SecurityProperties.dfy"

// ffi_usbtd_copy_from_user






