include ./config.mk

DAFNYTIMELIMIT ?= 4000
DAFNYFLAGS_NOARITH = /trace /stats /compile:0 /timeLimit:$(DAFNYTIMELIMIT)

DAFNY = $(DAFNY_DIR)/Dafny.exe
DAFNY21 = $(DAFNY21_DIR)/Dafny.exe
VALE = $(VALE_DIR)/vale.exe -includeSuffix .vad .gen.dfy

.PHONY: verify mk_verify_result_dir

verify: verify-dfy 

verify-dfy: \
	BuildCAS/BuildCAS.dfy.no_arith \
	BuildCAS/ReachableTDs.dfy.no_arith \
	BuildCAS/ReachableTDsStates.dfy.no_arith \
	BuildCAS/ReachableTDsStates_Utils.dfy.no_arith \
	BuildCAS/Utils_BuildCAS.dfy.no_arith \
	utils/Collections.dfy.no_arith \
	CASOps.dfy.no_arith \
	HCodedTD_Ops.dfy.no_arith \
	Lemmas.dfy.no_arith \
	Lemmas_Ops.dfy.no_arith \
	Lemmas_Ops_DrvDevRead.dfy.no_arith \
	Lemmas_SubjActivate_Ops.dfy.no_arith \
	Lemmas_SubjActivate_ReachableTDsStates.dfy.no_arith \
	Lemmas_SubjDeactivate_Ops.dfy.no_arith \
	Lemmas_SubjDeactivate_ReachableTDsStates.dfy.no_arith \
	Model.dfy.no_arith \
	Properties.dfy.no_arith \
	Properties_Corollaries.dfy.no_arith \
	Properties_Utils.dfy.no_arith \
	SecurityProperties.dfy.no_arith \
	SecurityProperties_Ops.dfy.no_arith \
	Syntax.dfy.no_arith \
	Utils.dfy.no_arith \
	Utils_SlimState.dfy.no_arith \

mk_verify_result_dir:
	$(MKDIR_DIR)/mkdir.exe -p result
	$(MKDIR_DIR)/mkdir.exe -p result/BuildCAS
	$(MKDIR_DIR)/mkdir.exe -p result/utils


# Verifications using more arith-related axioms
%.dfy.arith: %.dfy   | mk_verify_result_dir   # depend on folder creation is done
	-$(DAFNY) $(DAFNYFLAGS_ARITH) /compile:0 $< >result/$<.txt

# Verifications do not need any arith-related axioms
%.dfy.no_arith: %.dfy  | mk_verify_result_dir # depend on folder creation is done
	-$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 $< >result/$<.txt

clean:
	-rm -f *.dll *.mdb *.S *.exe *.pdb
	-rm -rf result
	


# Test purpose
.PHONY: v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
%.dfy.test.no_arith: %.dfy
	$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 $<

%.dfy.test.arith: %.dfy
	$(DAFNY) $(DAFNYFLAGS_ARITH) /compile:0 $<



v1: test.dfy.test.no_arith
v2: test2.dfy.test.no_arith
v3: test3.dfy.test.no_arith
#v4: test4.dfy.test.no_arith

#v2: Utils_Slimstate.dfy.test.no_arith
#v3: Utils.dfy.test.no_arith
v4: HcodedTD_Ops.dfy.test.no_arith
v5: Lemmas.dfy.test.no_arith
v6: BuildCAS/Utils_BuildCAS.dfy.test.no_arith
v7: Properties_Utils.dfy.test.no_arith
v8: BuildCAS/ReachableTDs.dfy.test.no_arith
v9: BuildCAS/ReachableTDsStates_Utils.dfy.test.no_arith
v10: BuildCAS/ReachableTDsStates.dfy.test.no_arith
v11: Properties.dfy.test.no_arith
v12: CASOps.dfy.test.no_arith
v13: Properties_Corollaries.dfy.test.no_arith
v14: Lemmas_Ops.dfy.test.no_arith
v15: BuildCAS/BuildCAS.dfy.test.no_arith

v16: Lemmas_SubjActivate_ReachableTDsStates.dfy.test.no_arith
v17: Lemmas_SubjActivate_Ops.dfy.test.no_arith
v18: Lemmas_SubjDeactivate_ReachableTDsStates.dfy.test.no_arith
v19: Lemmas_SubjDeactivate_Ops.dfy.test.no_arith #TODO

v20: SecurityProperties_Ops.dfy.test.no_arith
v21: Model.dfy.test.no_arith #TODO
v22: SecurityProperties.dfy.test.no_arith

.PHONY: c
c: 
	grep -RsIn "error" ./result
