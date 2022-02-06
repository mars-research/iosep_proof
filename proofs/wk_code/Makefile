include ./config.mk

DAFNYTIMELIMIT ?= 4000
DAFNYFLAGS_ARITH = /trace /errorTrace:0 /timeLimit:$(DAFNYTIMELIMIT) /ironDafny /allocated:1 /induction:1 /arith:10
DAFNYFLAGS_NOARITH = /trace /errorTrace:0 /timeLimit:$(DAFNYTIMELIMIT) /ironDafny /allocated:1 /induction:1 /noNLarith

DAFNY = $(DAFNY_DIR)/Dafny.exe
DAFNY21 = $(DAFNY21_DIR)/Dafny.exe
VALE = $(VALE_DIR)/vale.exe -includeSuffix .vad .gen.dfy

.PHONY: verify mk_verify_result_dir

verify: verify-vad verify-vad-dafny21 verify-dfy 

verify-dfy: \
	arch/common/arch_mem.dfy.no_arith \
	arch/common/arch_mem.i.dfy.no_arith \
	arch/x86/x86_cpu.dfy.no_arith \
	arch/x86/x86_cpu.i.dfy.no_arith \
	arch/x86/x86_globals.dfy.no_arith \
	arch/x86/x86_mem.dfy.no_arith \
	arch/x86/x86_mstate.dfy.no_arith \
	arch/x86/x86_types.dfy.no_arith \
	arch/headers.dfy.no_arith \
	arch/types.dfy.no_arith \
	arch/x86.dfy.no_arith \
	dev/usb2/usb_tds_ops/secure_usbtd.i.dfy.no_arith \
	dev/usb2/usb_tds_ops/usb_tds_checks.i.dfy.no_arith \
	dev/usb2/usb_tds_ops/usb_tds_checks.s.dfy.no_arith \
	dev/usb2/usb_tds_ops/usb_tds_ops.i.dfy.no_arith \
	dev/usb2/ffi/ehci.ffi.i.dfy.no_arith \
	dev/usb2/ffi/ehci.ffi.s.dfy.no_arith \
	dev/usb2/ffi/usb_tds.ffi.s.dfy.no_arith \
	dev/usb2/ffi/usb_tds.ffi.i.dfy.no_arith \
	dev/usb2/ffi/usbpdev.ffi.s.dfy.no_arith \
	dev/usb2/ffi/usbpdev.ffi.i.dfy.no_arith \
	dev/usb2/public/usb_lemmas.i.dfy.no_arith \
	dev/usb2/state_mapping/eehci_map.s.dfy.no_arith \
	dev/usb2/state_mapping/usbtd_map.s.dfy.no_arith \
	dev/usb2/eehci_info.i.dfy.no_arith \
	dev/usb2/eehci_mem_nlarith.i.dfy.arith \
	dev/usb2/eehci_mem.i.dfy.no_arith \
	dev/usb2/eehci_validstate.i.dfy.no_arith \
	dev/usb2/eehci.s.dfy.no_arith \
	dev/usb2/usb_def.dfy.no_arith \
	dev/usb2/usb_pdev_nlarith.i.dfy.arith \
	dev/usb2/usb_pdev_nlarith.noarith.i.dfy.no_arith \
	dev/usb2/usb_pdev_utils.i.dfy.no_arith \
	dev/usb2/usb_pdev_validstate.i.dfy.no_arith \
	dev/usb2/usb_pdev.i.dfy.no_arith \
	dev/usb2/usb_pdev.s.dfy.no_arith \
	dev/usb2/usb_tds_nlarith.i.dfy.arith \
	dev/usb2/usb_tds_nlarith.noarith.i.dfy.no_arith \
	dev/usb2/usb_tds_utils.i.dfy.no_arith \
	dev/usb2/usb_tds_validstate.i.dfy.no_arith \
	dev/usb2/usb_tds.i.dfy.no_arith \
	dev/usb2/usb_tds.s.dfy.no_arith \
	dev/usb2/usb.i.dfy.no_arith \
	drv/public/wimpdrv_lemmas.i.dfy.no_arith \
	drv/public/wimpdrv_util_predicates.s.dfy.no_arith \
	drv/drv_ops_utils.i.dfy.no_arith \
	drv/drv.ffi.s.dfy.no_arith \
	drv/drv.i.dfy.no_arith \
	drv/drv.s.dfy.no_arith \
	ins/util/ffi.i.dfy.no_arith \
	ins/util/ffi.s.dfy.no_arith \
	ins/x86/ins_eval_def.dfy.no_arith \
	ins/x86/ins_eval.s.dfy.no_arith \
	ins/x86/valesupp.i.dfy.no_arith \
	mhv/mhv.ffi.i.dfy.no_arith \
	mhv/mhv.ffi.s.dfy.no_arith \
	mm/headers.dfy.no_arith \
	mm/wk_globals.dfy.no_arith \
	mm/wk_mem.dfy.no_arith \
	mm/wk_mem.i.dfy.no_arith \
	proof/DM_AdditionalPredicates.s.dfy.no_arith \
	proof/DM_AdditionalPropertiesLemmas.i.dfy.no_arith \
	proof/DM_Operations_Stubs.s.dfy.no_arith \
	proof/io_accesses.dfy.no_arith \
	proof/io_accesses_commutative_diagram.i.dfy.no_arith \
	proof/io_accesses_ops_lemmas.i.dfy.no_arith \
	proof/state_map_any_state.s.dfy.no_arith \
	proof/state_map_OpsSaneState.i.dfy.no_arith \
	proof/state_map_OpsSaneStateSubset.i.dfy.no_arith \
	proof/state_map_OpsSaneStateSubset.s.dfy.no_arith \
	proof/utils_os_accesses.i.dfy.no_arith \
	proof/utils_os_accesses.s.dfy.no_arith \
	proof/utils_wimp_accesses.s.dfy.no_arith \
	proof/wkapi_commutative_diagram.i.dfy.no_arith \
	utils/common/alignness.dfy.arith \
	utils/common/bitvector_uint.i.dfy.arith \
	utils/common/bitvector_uint.s.dfy.arith \
	utils/common/bitvectors_primitive.i.dfy.arith \
	utils/common/bitvectors.i.dfy.arith \
	utils/common/bitvectors.s.dfy.arith \
	utils/common/collections.s.dfy.arith \
	utils/common/headers.dfy.arith \
	utils/common/Maybe.dfy.arith \
	utils/common/nlarith.s.dfy.arith \
	utils/common/Seq.dfy.arith \
	utils/common/types.i.dfy.arith \
	utils/common/types.s.dfy.arith \
	utils/common/uint32_ops.s.dfy.arith \
	utils/common/words_and_bytes.s.dfy.no_arith \
	utils/model/headers_any_state.dfy.no_arith \
	utils/model/utils_hcoded_ids_any_state.s.dfy.no_arith \
	utils/model/utils_ids_any_state.s.dfy.no_arith \
	utils/model/utils_objaddrs.s.dfy.no_arith \
	utils/model/utils_objs_any_state.s.dfy.no_arith \
	utils/model/utils_objs_secure_state.i.dfy.no_arith \
	utils/model/utils_objs_secure_state.s.dfy.no_arith \
	utils/model/utils_objs_valid_state.s.dfy.no_arith \
	utils/model/utils_subjs_any_state.i.dfy.no_arith \
	utils/model/utils_subjs_any_state.s.dfy.no_arith \
	utils/model/utils_subjs_valid_state.s.dfy.no_arith \
	utils/model/utils_subjs_objs.i.dfy.no_arith \
	partition_id.i.dfy.no_arith \
	partition_id.s.dfy.no_arith \
	state_properties_OpsSaneStateSubset.i.dfy.no_arith \
	state_properties_OpsSaneStateSubset.s.dfy.no_arith \
	state_properties_validity_subjs_objs_mstate.s.dfy.no_arith \
	state_properties_validity.i.dfy.no_arith \
	state_properties_validity.s.dfy.no_arith \
	state_properties.s.dfy.no_arith \
	state_utils.s.dfy.no_arith \
	SecurityProperties.dfy.no_arith \
	SecurityProperties_Ops.dfy.no_arith \
	state.dfy.no_arith \
	transition_constraints.s.dfy.no_arith \
	wk_ops_commons.dfy.no_arith \
	wk_partition_ops_utils.s.dfy.no_arith \

verify-vad: | v-gen \
	dev/usb2/usb_tds_ops/usb_tds_checks_qh.gen.dfy.no_arith \
	dev/usb2/usb_tds_ops/usb_tds_checks_qtd.gen.dfy.no_arith \
	dev/usb2/usb_tds_ops/usb_tds_checks.gen.dfy.no_arith \
	dev/usb2/usb_tds_ops/usb_tds_ops.private.gen.dfy.no_arith \
	dev/usb2/usb_tds_ops/usb_tds_ops.gen.dfy.no_arith \
	dev/usb2/usb_tds_ops/usb_tds_ops_impl.gen.dfy.no_arith \
	dev/usb2/usb_tds_ops/usb_tds_qhs_ops_impl.gen.dfy.no_arith \
	dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.gen.dfy.no_arith \
	dev/usb2/eehci_info.gen.dfy.no_arith \
	dev/usb2/eehci_mem_utils.gen.dfy.no_arith \
	dev/usb2/eehci_ops.gen.dfy.no_arith \
	dev/usb2/eehci_ops_impl.gen.dfy.no_arith \
	dev/usb2/eehci_ops_impl_private.gen.dfy.no_arith \
	dev/usb2/usb_pdev_ops.gen.dfy.no_arith \
	dev/usb2/usb_pdev_ops_impl.gen.dfy.no_arith \
	dev/usb2/usb_pdev_utils.gen.dfy.no_arith \
	dev/usb2/usb_tds_utils.gen.dfy.no_arith \
	drv/drv_ops.gen.dfy.no_arith \
	drv/drv_ops_impl.gen.dfy.no_arith \
	drv/drv_ops_impl_wimpdrv_activate.gen.dfy.no_arith \
	drv/drv_ops_utils.gen.dfy.no_arith \
	ins/x86/ins_utils.gen.dfy.no_arith \
	ins/x86/ins_wrapper.gen.dfy.no_arith \
	ins/x86/ins.gen.dfy.no_arith \
	os/os_ops.gen.dfy.no_arith \
	os/os_ops_impl.gen.dfy.no_arith \
	partition_id_ops.gen.dfy.no_arith \
	wk_partition_ops.gen.dfy.no_arith \
	wk_partition_ops_impl.gen.dfy.no_arith \

verify-vad-dafny21: | v-gen \
	dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.gen.dfy.no_arith.dafny21 \
	dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.gen.dfy.no_arith.dafny21 \
	dev/usb2/usb_tds_ops/usb_tds_qtds_ops.dafny21.gen.dfy.no_arith.dafny21 \

mk_verify_result_dir:
	$(MKDIR_DIR)/mkdir.exe -p result
	$(MKDIR_DIR)/mkdir.exe -p result/arch
	$(MKDIR_DIR)/mkdir.exe -p result/arch/common
	$(MKDIR_DIR)/mkdir.exe -p result/arch/x86
	$(MKDIR_DIR)/mkdir.exe -p result/dev
	$(MKDIR_DIR)/mkdir.exe -p result/dev/intr
	$(MKDIR_DIR)/mkdir.exe -p result/dev/usb2
	$(MKDIR_DIR)/mkdir.exe -p result/dev/usb2/ffi
	$(MKDIR_DIR)/mkdir.exe -p result/dev/usb2/public
	$(MKDIR_DIR)/mkdir.exe -p result/dev/usb2/state_mapping
	$(MKDIR_DIR)/mkdir.exe -p result/dev/usb2/usb_tds_ops
	$(MKDIR_DIR)/mkdir.exe -p result/drv
	$(MKDIR_DIR)/mkdir.exe -p result/drv/public
	$(MKDIR_DIR)/mkdir.exe -p result/ins
	$(MKDIR_DIR)/mkdir.exe -p result/ins/util
	$(MKDIR_DIR)/mkdir.exe -p result/ins/x86
	$(MKDIR_DIR)/mkdir.exe -p result/mhv
	$(MKDIR_DIR)/mkdir.exe -p result/mm
	$(MKDIR_DIR)/mkdir.exe -p result/os
	$(MKDIR_DIR)/mkdir.exe -p result/proof
	$(MKDIR_DIR)/mkdir.exe -p result/utils
	$(MKDIR_DIR)/mkdir.exe -p result/utils/common
	$(MKDIR_DIR)/mkdir.exe -p result/utils/model



%.gen.dfy: %.vad
	$(VALE) -in $< -out $@


# Verifications using more arith-related axioms
%.dfy.arith: %.dfy   | mk_verify_result_dir   # depend on folder creation is done
	-$(DAFNY) $(DAFNYFLAGS_ARITH) /compile:0 $< >result/$<.txt

# Verifications do not need any arith-related axioms
%.dfy.no_arith: %.dfy  | mk_verify_result_dir # depend on folder creation is done
	-$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 $< >result/$<.txt

%.dfy.no_arith.dafny21: %.dfy  | mk_verify_result_dir # depend on folder creation is done
	-$(DAFNY21) $(DAFNYFLAGS_NOARITH) /compile:0 $< >result/$<.txt

.PHONY: main.S main.exe
main.exe: main.dfy | v-gen
	$(DAFNY) $(DAFNYFLAGS_NOARITH) /noVerify /compile:2 /out:$@ $<

main.S: main.exe
	$(MONO) $< > $@

clean:
	-rm -f *.dll *.mdb *.S *.exe *.pdb
	-rm -f *.gen.dfy ins/x86/*.gen.dfy dev/usb2/*.gen.dfy dev/usb2/usb_tds_ops/*.gen.dfy mm/*.gen.dfy drv/*.gen.dfy os/*.gen.dfy
	-rm -rf result
	


# Test purpose
.PHONY: v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
%.dfy.test.no_arith: %.dfy
	$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 $<

%.dfy.test.arith: %.dfy
	$(DAFNY) $(DAFNYFLAGS_ARITH) /compile:0 $<




#v: dev/usb2/pci.s.dfy.test.no_arith
#v: state.dfy.test.no_arith
#v: dev/usb2/eehci_rw.ffi.x86.dfy.test.no_arith
#v: dev/usb2/eehci.s.dfy.test.no_arith

#v: mm/wk_mm_defs.dfy.test.no_arith
#v: INTELdef.s.dfy.test.no_arith
#v: utils/common/bitvectors.i.dfy.test.arith
#v: utils/common/bitvectors.s.dfy.test.arith
#v6: utils/common/nlarith.s.dfy.test.arith
#v6: utils/common/types.s.dfy.test.arith
#v6: utils/common/uint32_ops.s.dfy.test.arith
#v6: utils/common/alignness.dfy.test.arith
#v4: utils/common/types.i.dfy.test.arith

#v: utils/bitvectors_primitive.i.dfy.test.arith
#v4: arch/x86/x86_mem.dfy.test.no_arith
#v: arch/x86/x86_cpu.i.dfy.test.no_arith
#v: arch/x86.dfy.test.no_arith
#v: arch/common/arch_mem.dfy.test.no_arith
#v: mm/wk_mem.dfy.test.no_arith
#v8: mm/wk_globals.dfy.test.no_arith
#v: utils/common/headers.dfy.test.no_arith
#v: test1.dfy.test.arith

#v: partition_id.s.dfy.test.no_arith
#v: partition_id.i.dfy.test.no_arith

#v6: ins/x86/valesupp.i.dfy.test.no_arith
#v: ins/x86/ins_eval_def.dfy.test.no_arith
v3: ins/x86/ins_eval.s.dfy.test.no_arith
#v: ins/x86/ins_eval.i.dfy.test.no_arith
#v6: ins/util/ffi.s.dfy.test.no_arith
v4: ins/util/ffi.i.dfy.test.no_arith

#v3: dev/usb2/ffi/ehci.ffi.s.dfy.test.no_arith
#v14: dev/usb2/ffi/ehci.ffi.i.dfy.test.no_arith
v6: dev/usb2/ffi/usb_tds.ffi.s.dfy.test.no_arith
#v8: dev/usb2/ffi/usb_tds.ffi.i.dfy.test.no_arith
#v8: dev/usb2/ffi/usbpdev.ffi.s.dfy.test.no_arith
#v8: dev/usb2/ffi/usbpdev.ffi.i.dfy.test.no_arith

#v8: dev/usb2/usb_def.dfy.test.no_arith
#v8: dev/usb2/usb.i.dfy.test.no_arith
#v6: dev/usb2/eehci_info.i.dfy.test.no_arith

#v11: dev/usb2/eehci_mem.i.dfy.test.no_arith
#v11: dev/usb2/usb_tds_utils.i.dfy.test.no_arith
#v12: dev/usb2/usb_pdev.s.dfy.test.no_arith
#v13: dev/usb2/usb_pdev.i.dfy.test.no_arith
#v14: dev/usb2/usb_pdev_validstate.i.dfy.test.no_arith
#v14: dev/usb2/usb_tds_validstate.i.dfy.test.no_arith
#v7: dev/usb2/usb_pdev_nlarith.i.dfy.test.arith
#v7: dev/usb2/usb_pdev_nlarith.noarith.i.dfy.test.no_arith
#v7: dev/usb2/usb_tds_nlarith.i.dfy.test.arith
#v7: dev/usb2/usb_tds_nlarith.noarith.i.dfy.test.no_arith
#v7: dev/usb2/eehci_mem_nlarith.i.dfy.test.arith
#v7: dev/usb2/state_mapping/usbtd_map.s.dfy.test.arith
#v8: dev/usb2/usb_tds.i.dfy.test.no_arith
#v6: dev/usb2/usb_tds.s.dfy.test.no_arith
#v11: dev/usb2/usb_tds_ops/usb_tds_checks.s.dfy.test.no_arith
#v7: dev/usb2/usb_tds_ops/usb_tds_checks.i.dfy.test.no_arith
#v7: dev/usb2/usb_tds_ops/secure_usbtd.i.dfy.test.no_arith


#v4: test1.dfy.test.arith

v18: SecurityProperties_Ops.dfy.test.no_arith
v19: SecurityProperties.dfy.test.no_arith
v21: test/test.dfy.test.no_arith
v22: test/test2.dfy.test.no_arith
v23: test/test3.dfy.test.no_arith



v13: mhv/mhv.ffi.i.dfy.test.no_arith
#v7: drv/public/wimpdrv_lemmas.i.dfy.test.no_arith
#v7: drv/drv.i.dfy.test.no_arith
#v6: drv/drv.s.dfy.test.no_arith
#v6: drv/drv.ffi.s.dfy.test.no_arith
#v6: drv/drv.ffi.i.dfy.test.no_arith



#v6: proof/DM_Operations_Stubs.s.dfy.test.no_arith
v6: proof/io_accesses.dfy.test.no_arith
#v6: proof/io_accesses_ops_lemmas.i.dfy.test.no_arith
#v7: proof/utils_subjs_any_state.s.dfy.test.no_arith
v7: proof/state_map_OpsSaneStateSubset.s.dfy.test.no_arith
v8: proof/state_map_OpsSaneStateSubset.i.dfy.test.no_arith
#v7: proof/state_map_OpsSaneState.i.dfy.test.no_arith
#v6: proof/state_map_any_state.s.dfy.test.no_arith
#v9: proof/wkapi_commutative_diagram.i.dfy.test.no_arith

#v7: utils/model/utils_subjs_valid_state.s.dfy.test.no_arith
#v7: utils/model/utils_subjs_any_state.s.dfy.test.no_arith
#v8: utils/model/utils_objs_any_state.s.dfy.test.no_arith
#v8: utils/model/utils_objs_valid_state.s.dfy.test.no_arith
#v8: utils/model/utils_hcoded_ids_any_state.s.dfy.test.no_arith

#v5: test1.dfy.test.no_arith
v10: state_properties_OpsSaneStateSubset.s.dfy.test.no_arith
#v6: state_properties_validity.i.dfy.test.no_arith
#v9: state_properties_validity.s.dfy.test.no_arith
#v9: state_properties.s.dfy.test.no_arith
#v9: state_properties_OpsSaneStateSubset.i.dfy.test.no_arith
v9: transition_constraints.s.dfy.test.no_arith 

#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 ins/x86/ins.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 ins/x86/ins_wrapper.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 ins/x86/ins_utils.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 partition_id_ops.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/eehci_info.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/eehci_mem.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_tds_ops/usb_tds_ops.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_tds_ops/usb_tds_checks.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_tds_ops/usb_tds_checks_qtd.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_tds_ops/usb_tds_checks_qh.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_tds_utils.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/eehci_ops.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_pdev_ops.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_pdev_utils.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/test.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 drv/drv_ops_impl.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 drv/drv_ops_utils.gen.dfy
#$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 os/os_ops_impl.gen.dfy

.PHONY: v-gen vv1 vv2 vv3 vv4 vv5 vv6 vv7
vv1: 
	$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 test/test.gen.dfy

vv2: 
	$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 test/test2.gen.dfy

vv3: 
	$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 test/test3.gen.dfy

vv4: 
	$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 test/test4.gen.dfy

vv5: 
	$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 ins/x86/ins.gen.dfy

vv6: 
	$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 drv/drv_ops_impl_wimpdrv_activate.gen.dfy

vv7: 
	$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_tds_utils.gen.dfy

#v4: 
#	$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_tds_ops/usb_tds_qhs_ops_impl.gen.dfy


#$(DAFNY21) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.gen.dfy
.PHONY: v1-21 v2-21 v3-21
v1-21: 
	$(DAFNY21) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_tds_ops/usb_tds_qtds_ops.dafny21.gen.dfy


v2-21: 
	$(DAFNY21) $(DAFNYFLAGS_NOARITH) /compile:0 dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.gen.dfy

v3-21: 
	$(DAFNY21) $(DAFNYFLAGS_NOARITH) /compile:0 test/test.gen.dfy




#v-gen: ins/x86/ins.gen.dfy
#v-gen: utils/ins/utils.gen.dfy
.PHONY: v-gen
v-gen: \
	dev/usb2/usb_tds_ops/usb_tds_checks_qh.gen.dfy \
	dev/usb2/usb_tds_ops/usb_tds_checks_qtd.gen.dfy \
	dev/usb2/usb_tds_ops/usb_tds_checks.gen.dfy \
	dev/usb2/usb_tds_ops/usb_tds_ops.private.gen.dfy \
	dev/usb2/usb_tds_ops/usb_tds_ops.gen.dfy \
	dev/usb2/usb_tds_ops/usb_tds_ops_impl.gen.dfy \
	dev/usb2/usb_tds_ops/usb_tds_qhs_ops_impl.gen.dfy \
	dev/usb2/usb_tds_ops/usb_tds_qhs_ops.dafny21.gen.dfy \
	dev/usb2/usb_tds_ops/usb_tds_ops.dafny21.gen.dfy \
	dev/usb2/usb_tds_ops/usb_tds_qtds_ops.dafny21.gen.dfy \
	dev/usb2/usb_tds_ops/usb_tds_qtds_ops_impl.gen.dfy \
	dev/usb2/usb_tds_utils.gen.dfy \
	dev/usb2/usb_pdev_ops.gen.dfy \
	dev/usb2/usb_pdev_ops_impl.gen.dfy \
	dev/usb2/usb_pdev_utils.gen.dfy \
	dev/usb2/eehci_mem_utils.gen.dfy \
	dev/usb2/eehci_ops.gen.dfy \
	dev/usb2/eehci_ops_impl.gen.dfy \
	dev/usb2/eehci_ops_impl_private.gen.dfy \
	dev/usb2/eehci_info.gen.dfy \
	drv/drv_ops.gen.dfy \
	drv/drv_ops_impl.gen.dfy \
	drv/drv_ops_impl_wimpdrv_activate.gen.dfy \
	drv/drv_ops_utils.gen.dfy \
	ins/x86/ins_utils.gen.dfy \
	ins/x86/ins_wrapper.gen.dfy \
	ins/x86/ins.gen.dfy \
	os/os_ops.gen.dfy \
	os/os_ops_impl.gen.dfy \
	partition_id_ops.gen.dfy \
	wk_partition_ops.gen.dfy \
	wk_partition_ops_impl.gen.dfy \
	test/test.gen.dfy \
	test/test2.gen.dfy \
	test/test3.gen.dfy \
	test/test4.gen.dfy \




.PHONY: c
c: 
	grep -RsIn "error" ./result
