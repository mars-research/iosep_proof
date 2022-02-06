include ./config.mk

DAFNYTIMELIMIT ?= 4000
DAFNYFLAGS_NOARITH = /trace /stats /compile:0 /timeLimit:$(DAFNYTIMELIMIT)

DAFNY = $(DAFNY_DIR)/Dafny.exe
DAFNY21 = $(DAFNY21_DIR)/Dafny.exe
VALE = $(VALE_DIR)/vale.exe -includeSuffix .vad .gen.dfy

.PHONY: verify mk_verify_result_dir

verify: verify-dfy 

verify-dfy: \
	utils/Collections.dfy.no_arith \
	DevHWProt_Func.dfy.no_arith \
	HCodedTD_Ops.dfy.no_arith \
	K_AdditionalPropertiesLemmas.dfy.no_arith \
	K_Operations_Stubs.dfy.no_arith \
	Lemmas_ClosuresCombination.dfy.no_arith \
	Lemmas_DevHWProt.dfy.no_arith \
	Lemmas_Model_InnerFuncs.dfy.no_arith \
	Lemmas_Ops_Common.dfy.no_arith \
	Lemmas_Ops_GreenDrvWrite_SI1.dfy.no_arith \
	Lemmas_Ops_SI1_Common.dfy.no_arith \
	Lemmas_Ops_SubjObjActivate.dfy.no_arith \
	Lemmas_Ops_SubjObjDeactivate.dfy.no_arith \
	Lemmas_Ops_SubjRead.dfy.no_arith \
	Lemmas_Ops_SubjWrite.dfy.no_arith \
	Lemmas_SecureDMState.dfy.no_arith \
	Lemmas_SecureDMState_DevHWProt.dfy.no_arith \
	Mappings_ValidState_SecureState.dfy.no_arith \
	Model.dfy.no_arith \
	Model_InnerFuncs.dfy.no_arith \
	Model_Ops_Predicates.dfy.no_arith \
	Properties_DevHWProt.dfy.no_arith \
	Properties_SecureDMState.dfy.no_arith \
	Properties_ValidDMState.dfy.no_arith \
	SecurityProperties.dfy.no_arith \
	SecurityProperties_Ops.dfy.no_arith \
	Syntax.dfy.no_arith \
	Util_Lemmas.dfy.no_arith \
	Utils.dfy.no_arith \
	Utils_DevsActivateCond.dfy.no_arith \

mk_verify_result_dir:
	$(MKDIR_DIR)/mkdir.exe -p result
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
.PHONY: v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
%.dfy.test.no_arith: %.dfy
	$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 $<

%.dfy.test.arith: %.dfy
	$(DAFNY) $(DAFNYFLAGS_ARITH) /compile:0 $<



v1: test1.dfy.test.no_arith
v2: test2.dfy.test.no_arith
v3: test3.dfy.test.no_arith
v4: test4.dfy.test.no_arith
v5: test5.dfy.test.no_arith
v6: test6.dfy.test.no_arith
v7: test7.dfy.test.no_arith

#v1: Utils.dfy.test.no_arith
#v2: K_AdditionalPropertiesLemmas.dfy.test.no_arith
#v3: HcodedTD_Ops.dfy.test.no_arith
#v4: Properties_ValidDMState.dfy.test.no_arith
#v5: Utils_DevsActivateCond.dfy.test.no_arith
#v6: Util_Lemmas.dfy.test.no_arith
#v7: Lemmas_Ops_Common.dfy.test.no_arith
v8: Properties_DevHWProt.dfy.test.no_arith
v9: Properties_SecureDMState.dfy.test.no_arith
v10: Lemmas_ClosuresCombination.dfy.test.no_arith
v11: Lemmas_DevHWProt.dfy.test.no_arith
v12: Lemmas_Ops_GreenDrvWrite_SI1.dfy.test.no_arith
v13: Lemmas_Ops_SI1_Common.dfy.test.no_arith
v14: Lemmas_Ops_SubjObjActivate.dfy.test.no_arith
v15: Model_Ops_Predicates.dfy.test.no_arith
v16: Lemmas_Ops_SubjObjDeactivate.dfy.test.no_arith
v17: Lemmas_Ops_SubjRead.dfy.test.no_arith
v18: Lemmas_Ops_SubjWrite.dfy.test.no_arith
v19: Lemmas_SecureDMState.dfy.test.no_arith
v20: Lemmas_SecureDMState_DevHWProt.dfy.test.no_arith
v21: Mappings_ValidState_SecureState.dfy.test.no_arith
v22: Model_InnerFuncs.dfy.test.no_arith
v23: SecurityProperties_Ops.dfy.test.no_arith

v24: SecurityProperties.dfy.test.no_arith
v25: Lemmas_Model_InnerFuncs.dfy.test.no_arith
v26: Model.dfy.test.no_arith 


.PHONY: c
c: 
	grep -RsIn "error" ./result
