Run verification
==================================
Dafny 2.3 (650a6bbe): https://github.com/dafny-lang/dafny
Vale-v0.3.10: https://github.com/project-everest/vale/releases/tag/v0.3.10

Machine: i9-9900K + 128GB memory
Command: make verify -j16


Definitions
==================================
1. State: state.dfy
2. State invariants: state_properties.s.dfy
3. Transition Constraints: transition_constraints.s.dfy
4. Direct I/O accesses: proof/io_accesses.dfy
5. WK APIs: wk_partition_ops.vad, drv/drv_ops.vad, dev/usb2/eehci_ops.vad, dev/usb2/usb_pdev_ops.vad, 
            dev/usb2/usb_tds_ops/usb_tds_ops.vad


Line count
==================================
Result: 54771 (*.dfy) + 26618 (*.vad) = 81389
Command: find . -name '*.dfy' | xargs wc -l
         find . -name '*.vad' | xargs wc -l

LOC of output assembly file: 12031
Command: find . -name 'main.S' | xargs wc -l


Additional model considerations too detailed to be included in paper
==================================
1. The current approach to prevent USB peripheral devices' address modification
    - Step 1. No physical hubs or ephemeral hubs can be given to wimp drivers
    - Step 2. No wimp drivers can submit USB IDSes to reset their USB peripheral devices
        - Assumption: the USB hierarchy addresses (called "address" below, comprising USB bus ID, USB address, 
        connected hub’s USB address, and hub port) of USB peripheral devices can only be modified by submitting USB IDSes.
2. The model does not contain physical USB hubs or ephemeral hubs; Physical EHCIs include all physical hubs, and no  
ephemeral hubs can be created.
    - Reason: No physical USB hubs or ephemeral USB hubs can be given to wimp drivers, or our current method of 
    preventing USB peripheral devices' address modification is invalid. This is because USB hubs can warm reset and cold
    reset its connected USB peripheral devices.


Additional Axioms (Reported in the paper but not in the code)
==================================
1. [API Atomicity] Axiom : I/O accesses and WK APIs must be atomic; i.e., no I/O accesses or other API calls can happen in the 
middle of an API call
    - WK implementation needs to do 2 things to fulfill this axiom
        (1) WK must clear (a) physical memory unassigned on-demand, (b) physical EHCIs and all their connected USB 
        peripheral devices before activating them in the OS partition. Thus, all I/O accesses issued in parallel with 
        WK API calls return the same results as if they are issued before or after the APIs. 
        (2) Only one WK API can be called at one time


Known issues
==================================
1. Dafny-v2.3 can verify the following functions alone, but report errors if they are defined with other functions. 
Future Dafny releases may solve the issue.
    - <_usbtd_slot_allocate_1slot_private> in dev/usb2/usb_tds_ops/usb_tds_ops_impl.vad
    - <_wimpdrv_find_referencing_secure_usbtd> in dev/usb2/usb_tds_ops/usb_tds_ops.private.vad


Limitations
==================================
1. If a wimp driver submits a set of USB TDs, which reference each other in a circle, then the current implementation 
cannot verify these USB TDs

2. Buffer pointers in USB TDs must always point to valid memory region, even when not used in USB transfers