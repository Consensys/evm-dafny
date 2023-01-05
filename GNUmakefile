ifneq (VERSION4.X, $(patsubst 4.%,VERSION4.X,$(MAKE_VERSION)))
  $(warning For best results, use GNU Make v4 or later!)
endif

#some defaults for sanity preservation
SHELL := bash
.SHELLFLAGS := -eu -o pipefail -c
.DELETE_ON_ERROR:
MAKEFLAGS += --warn-undefined-variables --no-builtin-rules
#each target has its own parallelism too, so keep a low number of jobs
MAKEFLAGS += -j 2 --output-sync
RUN_ARGS ?=

#silent by default
SILENCER := @
VERBOSE ?= 0
ifeq ($(VERBOSE),1)
	SILENCER :=
endif

.DEFAULT_GOAL := all

BUILD_DIR:=build
DAFNY_EXEC ?= dafny

DAFNY_SRC_DIR:=src/dafny
DAFNY_SRC_ENTRY_POINT:=src/dafny/t8n.dfy #src/dafny/evms/berlin.dfy
DAFNY_OUT_NAME:=dafnyexec
DAFNY_SRC_FILES:= $(shell find $(DAFNY_SRC_DIR) -type f -name '*.dfy')
DAFNY_OUT_ARG:=$(BUILD_DIR)/$(DAFNY_OUT_NAME)
DAFNY_OUT_DIR:=$(DAFNY_OUT_ARG)-go
DAFNY_OUT_FILENAME:=$(DAFNY_OUT_DIR)/src/$(DAFNY_OUT_NAME).go


###################### DAFNY VERIFY GLOBAL ########################
# Verify (without translation) all Dafny files in DAFNY_SRC_FILES, dropping a dotfile witness.

DAFNY_VERIFY_WITNESS_GLOBAL:=$(DAFNY_OUT_DIR)/.last_verify_all

dafny_verify_global: $(DAFNY_VERIFY_WITNESS_GLOBAL)

$(DAFNY_VERIFY_WITNESS_GLOBAL) : $(DAFNY_SRC_FILES)
	@echo Verifying Dafny
	$(SILENCER)$(DAFNY_EXEC) /vcsLoad:2 /compile:0 /rlimit:100000 $(DAFNY_SRC_FILES)
#	$(SILENCER)$(DAFNY_EXEC) verify --cores 4 -rlimit:100000 $(DAFNY_SRC_FILES)
	$(SILENCER)mkdir -p $(DAFNY_OUT_DIR)
	$(SILENCER)touch $@

dafny_verify_global_clean:
	@echo Removing verification witness
	$(SILENCER)$(RM) -f $(DAFNY_VERIFY_WITNESS_GLOBAL)

dafny_verify_global_force: dafny_verify_global_clean
	$(SILENCER)$(MAKE) dafny_verify_global



###################### DAFNY VERIFY INDIVIDUAL ########################
# Verify (without translation) each Dafny file in DAFNY_SRC_FILES, dropping a dotfile witness for each.

DAFNY_VERIFY_WITNESSES:=$(patsubst $(DAFNY_SRC_DIR)/%.dfy,$(DAFNY_OUT_DIR)/%.verified,$(DAFNY_SRC_FILES))

dafny_verify_individuals: $(DAFNY_VERIFY_WITNESSES)

$(DAFNY_OUT_DIR)/%.verified : $(DAFNY_SRC_DIR)/%.dfy
	@echo Verifying $<
	$(SILENCER)$(DAFNY_EXEC) /vcsLoad:2 /compile:0 /rlimit:100000 $< && mkdir -p $(shell dirname $@) && touch $@

dafny_verify_individuals_clean:
	@echo Removing verification witnesses
	$(SILENCER)$(RM) -f $(DAFNY_VERIFY_WITNESSES)

dafny_verify_individuals_force: dafny_verify_individuals_clean
	$(SILENCER)$(MAKE) dafny_verify_individuals



###################### DAFNY TRANSLATE INDIVIDUAL ########################
# Dafny can't really translate individual files, but we can approximate it.
# Translate (but don't verify) all the Dafny sources, using build product as witness.
# Checks that the individual verification was done already.

dafny_translate_individuals: $(DAFNY_OUT_FILENAME) $(DAFNY_VERIFY_WITNESSES)

$(DAFNY_OUT_FILENAME) : $(DAFNY_SRC_FILES)
	@echo Translating Dafny
	$(SILENCER)$(DAFNY_EXEC) /rlimit:100000 /vcsLoad:2 /compileTarget:go /compileVerbose:0 /compile:2 /spillTargetCode:3 /noExterns /warnShadowing /deprecation:2 /out:$(DAFNY_OUT_ARG) $(DAFNY_SRC_FILES)  /noVerify

dafny_translate_individuals_clean:
	@echo Removing Dafny products
	$(SILENCER)rm -rf $(DAFNY_OUT_FILENAME)

dafny_run: $(DAFNY_OUT_FILENAME)
	$(SILENCER)GO111MODULE=off GOPATH=`readlink -f $(DAFNY_OUT_DIR)` go run $(DAFNY_OUT_FILENAME) $(RUN_ARGS)



###################### DAFNY TEST INDIVIDUAL ########################
# Verify & run Dafny tests file by file, using each build output as a witness.

DAFNY_TEST_DIR:=src/test/dafny
DAFNY_TEST_FILES:= $(shell find $(DAFNY_TEST_DIR) -type f -name '*.dfy')
DAFNY_TEST_OUT_DIR:=$(BUILD_DIR)/dafny-tests
#DAFNY_TEST_PRODS_DIR:=$(DAFNY_TEST_OUT_ARG)-go
DAFNY_TEST_WITNESSES:=$(patsubst $(DAFNY_TEST_DIR)/%.dfy,$(DAFNY_TEST_OUT_DIR)/.%-go,$(DAFNY_TEST_FILES))

dafny_test_individuals: $(DAFNY_TEST_WITNESSES)

#TODO probably tests should refer to the main build instead of rebuilding it
$(DAFNY_TEST_OUT_DIR)/.%-go : $(DAFNY_TEST_DIR)/%.dfy $(DAFNY_SRC_FILES)
	@echo Testing Dafny: $<
	$(SILENCER)$(DAFNY_EXEC) /runAllTests:1 /vcsLoad:2  /compileTarget:go /compile:4 /compileVerbose:0 /noExterns /out:$(DAFNY_TEST_OUT_DIR)/$* $<
	$(SILENCER)touch $@

dafny_test_individuals_clean:
	@echo Removing test witnesses
	$(SILENCER)$(RM) -rf $(DAFNY_TEST_OUT_DIR)

dafny_test_individuals_force: dafny_test_individuals_clean
	$(SILENCER)$(MAKE) dafny_test



###################### DAFNY TEST GLOBAL ########################
# Verify & run all tests together, dropping a dotfile witness.

DAFNY_TEST_WITNESS_GLOBAL:=$(DAFNY_TEST_OUT_DIR)/.last_global_test

dafny_test_global: $(DAFNY_TEST_WITNESS_GLOBAL)

$(DAFNY_TEST_WITNESS_GLOBAL): $(DAFNY_TEST_FILES) $(DAFNY_SRC_FILES)
	$(SILENCER)$(DAFNY_EXEC)  /vcsLoad:2  /compileTarget:go /compile:3 /compileVerbose:0 /noExterns /out:$(DAFNY_TEST_OUT_DIR)/global $(DAFNY_TEST_FILES) /runAllTests:1 # /noVerify /compile:4
	$(SILENCER)touch $@

dafny_test_global_clean:
	@echo Removing global test witness
	$(SILENCER)$(RM) -rf $(DAFNY_TEST_WITNESS_GLOBAL)

dafny_test_global_force: dafny_test_global_clean
	$(SILENCER)$(MAKE) dafny_test_global


###################### DAFNY VERIFY & TRANSLATE GLOBAL ########################
# Verify and translate all the Dafny sources, using build product as witness.
# Mainly useful for CI; for normal usage we'll want to process individual files instead.

DAFNY_OUT_NAME_CI:=dafnyexecci
DAFNY_OUT_ARG_CI:=$(BUILD_DIR)/$(DAFNY_OUT_NAME_CI)
DAFNY_OUT_DIR_CI:=$(DAFNY_OUT_ARG_CI)-go
DAFNY_OUT_FILENAME_CI:=$(DAFNY_OUT_DIR_CI)/src/$(DAFNY_OUT_NAME_CI).go

dafny_translate_global: $(DAFNY_OUT_FILENAME_CI) $(DAFNY_VERIFY_WITNESS_GLOBAL)

$(DAFNY_OUT_FILENAME_CI) : $(DAFNY_SRC_FILES)
	@echo Verifying and translating Dafny
	$(SILENCER)$(DAFNY_EXEC) /rlimit:100000 /vcsLoad:2 /compileTarget:go /compileVerbose:0 /compile:4 /spillTargetCode:3 /noExterns /warnShadowing /deprecation:2 /out:$(DAFNY_OUT_ARG_CI) $(DAFNY_SRC_FILES)
	$(SILENCER)touch $(DAFNY_VERIFY_WITNESS_GLOBAL)

dafny_translate_global_clean:
	@echo Removing Dafny products
	$(SILENCER)rm -rf $(DAFNY_OUT_FILENAME_CI) $(DAFNY_VERIFY_WITNESS_GLOBAL)


###################### DAFNY GENERAL ########################
# During normal usage you'll want to process individual files whenever possible

dafny: dafny_translate dafny_test

dafny_translate : dafny_translate_individuals

dafny_verify : dafny_verify_individuals

dafny_verify_clean : dafny_verify_individuals_clean

dafny_test : dafny_test_individuals

dafny_test_clean : dafny_test_individuals_clean

dafny_clean: dafny_translate_individuals_clean dafny_test_clean dafny_verify_clean

###################### CI ########################
# For CI we can process all files at once. Also as sanity check vs the individual file hacks.

ci: dafny_translate_global dafny_test_global

###################### GO ########################

go:
	UNIMPLEMENTED

###################### MAKEFILE CLASSICS ########################

all: dafny #go

test: dafny_test

run: dafny_run

clean: dafny_clean #go_clean


.PHONY: clean all dafny dafny_clean dafny_translate_clean dafny_verify dafny_verify_force dafny_verify_clean dafny_run dafny_test dafny_test_clean dafny_test_force dafny_test_global dafny_test_global_clean dafny_test_global_force


