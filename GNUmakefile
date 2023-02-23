# Dafny doesn't give dependency information, so we need to do it our own way.
# In general,
#    Dafny "core" needs to be verified following deps (or all at once, of course).
#    Dafny tests depend on the core, are independent of each other, and are done faster all at once.
#    Dafny "main" entry points depend on the core and need to be compiled separately from tests and from each other.

ifneq (VERSION4.X, $(patsubst 4.%,VERSION4.X,$(MAKE_VERSION)))
  $(warning For best results, use GNU Make v4 or later!)
endif

#some defaults for sanity preservation
SHELL := bash
.SHELLFLAGS := -eu -o pipefail -c
.DELETE_ON_ERROR:
MAKEFLAGS += --warn-undefined-variables --no-builtin-rules
#each target has its own parallelism too, so keep a low number of jobs
MAKEFLAGS += -j 2 #--output-sync
RUN_ARGS ?=
DAFNY_ARGS := --function-syntax 4 --quantifier-syntax 4  --cores 50%

#silent by default
SILENCER := @
VERBOSE ?= 0
ifeq ($(VERBOSE),1)
	SILENCER :=
endif

.DEFAULT_GOAL := all

DAFNY_EXEC ?= dafny

DAFNY_SRC_DIR:=src/dafny
DAFNY_SRC_ENTRY_POINT:=src/dafny/t8n.dfy #src/dafny/evms/berlin.dfy
DAFNY_SRC_FILES:= $(shell find $(DAFNY_SRC_DIR) -type f -name '*.dfy')

BUILD_DIR:=build
DAFNY_OUT_NAME:=dafnyexec
# The dafny tool creates its output filename like this.
DAFNY_OUT_ARG:=$(BUILD_DIR)/$(DAFNY_OUT_NAME)
DAFNY_OUT_DIR:=$(DAFNY_OUT_ARG)-go
DAFNY_OUT_FILENAME:=$(DAFNY_OUT_DIR)/src/$(DAFNY_OUT_NAME).go

DAFNY_TEST_DIR:=src/test/dafny
DAFNY_TEST_FILES:= $(shell find $(DAFNY_TEST_DIR) -type f -name '*.dfy')
DAFNY_TEST_OUT_DIR:=$(BUILD_DIR)/dafny-tests
#DAFNY_TEST_PRODS_DIR:=$(DAFNY_TEST_OUT_ARG)-go


###################### DAFNY VERIFY GLOBAL ########################
# Verify (without translation) all Dafny files in DAFNY_SRC_FILES, dropping a dotfile witness.

DAFNY_VERIFY_WITNESS_GLOBAL:=$(DAFNY_OUT_DIR)/.last_verify_all

dafny_verify_global: $(DAFNY_VERIFY_WITNESS_GLOBAL)

$(DAFNY_VERIFY_WITNESS_GLOBAL) : $(DAFNY_SRC_FILES)
	@echo Verifying Dafny
#	$(SILENCER)$(DAFNY_EXEC) /vcsLoad:2 /compile:0 /rlimit:100000 /functionSyntax:4 /quantifierSyntax:4 $(DAFNY_ARGS) $(DAFNY_SRC_FILES)
	$(SILENCER)$(DAFNY_EXEC) verify $(DAFNY_ARGS) --verify-included-files --resource-limit 100000 $(DAFNY_SRC_FILES)
	$(SILENCER)mkdir -p $(DAFNY_OUT_DIR)
	$(SILENCER)touch $@

dafny_verify_global_clean:
	@echo Removing verification witness
	$(SILENCER)$(RM) -f $(DAFNY_VERIFY_WITNESS_GLOBAL)

dafny_verify_global_force: dafny_verify_global_clean
	$(SILENCER)$(MAKE) dafny_verify_global


###################### DAFNY TEST  ########################
# Verify & run all changed tests together, dropping a dotfile witness.
# Only re-does test files newer than the witness. Depends on the global verification.

DAFNY_TEST_WITNESS_GLOBAL:=$(DAFNY_TEST_OUT_DIR)/.last_global_test

dafny_test_global: $(DAFNY_TEST_WITNESS_GLOBAL) $(DAFNY_VERIFY_WITNESS_GLOBAL)

#TODO probably tests should refer to the main build instead of rebuilding it (once the Dafny toolchain supports it)
$(DAFNY_TEST_WITNESS_GLOBAL): $(DAFNY_TEST_FILES)
	@echo Testing Dafny : `echo $? | wc -w` files
	$(SILENCER)$(DAFNY_EXEC)  /vcsLoad:2  /compileTarget:go /compile:4 /compileVerbose:0 /noExterns /functionSyntax:4 /quantifierSyntax:4 /out:$(DAFNY_TEST_OUT_DIR)/global $? /runAllTests:1  /warnShadowing /deprecation:2 #$(DAFNY_ARGS)
#	Dafny v4 new CLI: test doesn't seem to work
#	$(SILENCER)$(DAFNY_EXEC) test $(DAFNY_ARGS) --test-assumptions Externs  --target go --warn-shadowing  --resource-limit 100000  $< # --output $(DAFNY_TEST_OUT_DIR)/$*
	$(SILENCER)touch $@

dafny_test_global_clean:
	@echo Removing global test witness
	$(SILENCER)$(RM) -rf $(DAFNY_TEST_WITNESS_GLOBAL)

dafny_test_global_force: dafny_test_global_clean
	$(SILENCER)$(MAKE) dafny_test_global


###################### DAFNY TRANSLATE MAINS ########################
# Translate Dafny Main's, using build product as witness.
# Depends on previous global verification.

dafny_translate: $(DAFNY_OUT_FILENAME) $(DAFNY_TEST_WITNESS_GLOBAL)

$(DAFNY_OUT_FILENAME) : $(DAFNY_SRC_FILES)
	@echo Translating Dafny
	$(SILENCER)$(DAFNY_EXEC) /rlimit:100000 /vcsLoad:2 /compileTarget:go /compileVerbose:0 /spillTargetCode:3 /noExterns /warnShadowing /deprecation:2 /functionSyntax:4 /quantifierSyntax:4 /out:$(DAFNY_OUT_ARG) $(DAFNY_SRC_ENTRY_POINT) /compile:2 #$(DAFNY_ARGS)
#	Dafny v4 new CLI: missing --deprecation and --noExterns
#	$(SILENCER)$(DAFNY_EXEC) build $(DAFNY_ARGS) --no-verify --target go --warn-shadowing --test-assumptions Externs --output:$(DAFNY_OUT_ARG) $(DAFNY_SRC_ENTRY_POINT) #--deprecation 2  -noExterns

dafny_translate_clean:
	@echo Removing Dafny products
	$(SILENCER)rm -rf $(DAFNY_OUT_FILENAME)


dafny_run: $(DAFNY_OUT_FILENAME)
	$(SILENCER)GO111MODULE=off GOPATH=`readlink -f $(DAFNY_OUT_DIR)` go run $(DAFNY_OUT_FILENAME) $(RUN_ARGS)

###################### DAFNY GENERAL ########################

dafny: dafny_verify dafny_translate dafny_test

dafny_verify : dafny_verify_global

dafny_verify_clean : dafny_verify_global_clean

dafny_test : dafny_test_global

dafny_test_clean : dafny_test_global_clean

dafny_clean: dafny_translate_clean dafny_test_clean dafny_verify_clean

###################### GO ########################

go:
	UNIMPLEMENTED

###################### MAKEFILE CLASSICS ########################

all: dafny #go

test: dafny_test

run: dafny_run

clean: dafny_clean #go_clean


.PHONY: clean all dafny dafny_clean dafny_translate_clean dafny_verify dafny_verify_force dafny_verify_clean dafny_run dafny_test dafny_test_clean dafny_test_force dafny_test_global dafny_test_global_clean dafny_test_global_force


