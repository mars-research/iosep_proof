include ./config.mk

DAFNYTIMELIMIT ?= 4000
DAFNYFLAGS_NOARITH = /trace /stats /compile:0 /timeLimit:$(DAFNYTIMELIMIT)

DAFNY = $(DAFNY_DIR)/Dafny.exe
DAFNY21 = $(DAFNY21_DIR)/Dafny.exe
VALE = $(VALE_DIR)/vale.exe -includeSuffix .vad .gen.dfy

.PHONY: verify mk_verify_result_dir

verify: verify-dfy verify-dfy-dafny21

verify-dfy: \
	DevActivate_Multi.dfy.no_arith \
	DevActivate_Multi_Mtd.dfy.no_arith \
	DM_AdditionalPropertiesLemmas.dfy.no_arith \
	Model.dfy.no_arith \
	SecurityProperties.dfy.no_arith \
	SecurityProperties_Ops.dfy.no_arith \
	Utils.dfy.no_arith \
	Utils.i.dfy.no_arith \

verify-dfy-dafny21 : \
	Utils.dafny21.dfy.no_arith.dafny21 \

mk_verify_result_dir:
	$(MKDIR_DIR)/mkdir.exe -p result


# Verifications using more arith-related axioms
%.dfy.arith: %.dfy   | mk_verify_result_dir   # depend on folder creation is done
	-$(DAFNY) $(DAFNYFLAGS_ARITH) /compile:0 $< >result/$<.txt

# Verifications do not need any arith-related axioms
%.dfy.no_arith: %.dfy  | mk_verify_result_dir # depend on folder creation is done
	-$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 $< >result/$<.txt

%.dfy.no_arith.dafny21: %.dfy  | mk_verify_result_dir # depend on folder creation is done
	-$(DAFNY21) $(DAFNYFLAGS_NOARITH) /compile:0 $< >result/$<.txt

clean:
	-rm -f *.dll *.mdb *.S *.exe *.pdb
	-rm -rf result
	


# Test purpose
.PHONY: v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
%.dfy.test.no_arith: %.dfy
	$(DAFNY) $(DAFNYFLAGS_NOARITH) /compile:0 $<

%.dfy.test.arith: %.dfy
	$(DAFNY) $(DAFNYFLAGS_ARITH) /compile:0 $<

.PHONY: v1-21 v2-21 v3-21
v1-21:
	$(DAFNY21) $(DAFNYFLAGS_NOARITH) /compile:0 Utils.dafny21.dfy

v2-21:
	$(DAFNY21) $(DAFNYFLAGS_NOARITH) /compile:0 test.dfy

v3-21:
	$(DAFNY21) $(DAFNYFLAGS_NOARITH) /compile:0 DevActivate_Multi_Mtd.dfy


v11: test.dfy.test.no_arith
v12: test2.dfy.test.no_arith
v13: test3.dfy.test.no_arith

v1: DM_AdditionalPropertiesLemmas.dfy.test.no_arith
v2: Utils.dfy.test.no_arith

v3: SecurityProperties_Ops.dfy.test.no_arith
v4: SecurityProperties.dfy.test.no_arith

v5: Model.dfy.test.no_arith
v6: DevActivate_Multi_Mtd.dfy.test.no_arith


.PHONY: c
c: 
	grep -RsIn "error" ./result
