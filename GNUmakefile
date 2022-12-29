ifneq (VERSION4.X, $(patsubst 4.%,VERSION4.X,$(MAKE_VERSION)))
  $(warning For best results, use GNU Make v4 or later!)
endif

#some defaults for sanity preservation
SHELL := bash
.SHELLFLAGS := -eu -o pipefail -c
.DELETE_ON_ERROR:
MAKEFLAGS += --warn-undefined-variables --no-builtin-rules
#each target has its own parallelism too
MAKEFLAGS += -j 2 --output-sync

#silent by default
SILENCER := @
VERBOSE ?= 0
ifeq ($(VERBOSE),1)
	SILENCER :=
endif

.DEFAULT_GOAL := dafny #go

# If the first Make argument is "run"...
MAKECMDGOALS ?=
ifeq (run,$(firstword $(MAKECMDGOALS)))
  # use the rest as arguments for "run"
  RUN_ARGS := $(wordlist 2,$(words $(MAKECMDGOALS)),$(MAKECMDGOALS))
  # ...and turn them into do-nothing targets
  $(eval $(RUN_ARGS):;@:)
endif



BUILD_DIR:=build
DAFNY_EXEC ?= dafny



###################### DAFNY TRANSLATE ########################

DAFNY_SRC_DIR:=src/dafny
DAFNY_SRC_FILES:= $(shell find $(DAFNY_SRC_DIR) -type f -name '*.dfy')
DAFNY_OUT_NAME:=dafny
DAFNY_OUT_ARG:=$(BUILD_DIR)/$(DAFNY_OUT_NAME)
DAFNY_OUT_DIR:=$(DAFNY_OUT_ARG)-go
DAFNY_OUT_FILENAME:=$(DAFNY_OUT_DIR)/src/$(DAFNY_OUT_NAME).go

dafny_translate: $(DAFNY_OUT_FILENAME)

$(DAFNY_OUT_FILENAME) : $(DAFNY_SRC_FILES)
	@echo 'Translating Dafny'
#	$(SILENCER)$(RM) -rf $(DAFNY_OUT_DIR)	# we don't know how to make it more granular, so at least let's ensure that the output is newer than the sources
#	$(SILENCER)$(DAFNY_EXEC) translate --cores 4 --no-verify --target go --output $(DAFNY_OUT_ARG) --compile-verbose src/dafny/evms/berlin.dfy
	$(SILENCER)$(DAFNY_EXEC) /rlimit:100000 /vcsLoad:2.5 /compileTarget:go /compileVerbose:1 /compile:2 /spillTargetCode:3 /noVerify /noExterns /out:$(DAFNY_OUT_ARG) src/dafny/evms/berlin.dfy


dafny_run: $(DAFNY_OUT_FILENAME)
#	$(SILENCER)cd $(DAFNY_OUT_DIR) && GO111MODULE=off GOPATH=`pwd` go run src/$(DAFNY_OUT_NAME).go
	$(SILENCER)GO111MODULE=off GOPATH=`readlink -f $(DAFNY_OUT_DIR)` go run $(DAFNY_OUT_FILENAME)

dafny_translate_clean:
	@echo Removing Dafny products
	$(SILENCER)rm -rf $(DAFNY_OUT_DIR)

###################### DAFNY VERIFY ########################

DAFNY_VERIFY_WITNESS:=$(DAFNY_OUT_DIR)/.last_verify_all

dafny_verify: $(DAFNY_VERIFY_WITNESS)

#$(info SECOND:$(DAFNY_VERIFY_WITNESS): $(DAFNY_SRC_FILES))
$(DAFNY_VERIFY_WITNESS) : $(DAFNY_SRC_FILES)
	@echo Verifying Dafny
#	$(SILENCER)$(DAFNY_EXEC) /vcsLoad:2.5 /compile:0 $(DAFNY_SRC_FILES)
	$(SILENCER)$(DAFNY_EXEC) verify --cores 4 --verification-time-limit 20 $(DAFNY_SRC_FILES)
	$(SILENCER)mkdir -p $(DAFNY_OUT_DIR)
	$(SILENCER)touch $@

dafny_verify_clean:
	@echo Removing verification witness
	$(SILENCER)$(RM) -f $(DAFNY_VERIFY_WITNESS)

dafny_verify_force: dafny_verify_clean
	$(SILENCER)$(MAKE) dafny_verify

###################### DAFNY TEST ########################
#TODO some "tests" are not executed but only verified. Clarify whether that's OK.
# Avoid /noVerify until then.

DAFNY_TEST_DIR:=src/test/dafny
DAFNY_TEST_FILES:= $(shell find $(DAFNY_TEST_DIR) -type f -name '*.dfy')
DAFNY_TEST_OUT_DIR:=$(BUILD_DIR)/dafny-tests
#DAFNY_TEST_PRODS_DIR:=$(DAFNY_TEST_OUT_ARG)-go
DAFNY_TEST_WITNESSES:=$(patsubst $(DAFNY_TEST_DIR)/%.dfy,$(DAFNY_TEST_OUT_DIR)/.%-go,$(DAFNY_TEST_FILES))

dafny_test: $(DAFNY_TEST_WITNESSES)

#for each DAFNY_TEST_WITNESSES...
#TODO probably tests should refer to the main build instead of rebuilding it
$(DAFNY_TEST_OUT_DIR)/.%-go : $(DAFNY_TEST_DIR)/%.dfy $(DAFNY_SRC_FILES)
	@echo Testing Dafny: $<
	$(SILENCER)$(DAFNY_EXEC) /runAllTests:1 /vcsLoad:2.5  /compileTarget:go /compile:4 /compileVerbose:0 /noExterns /out:$(DAFNY_TEST_OUT_DIR)/$* $<  #we don't really care where it goes, but each test needs its own dir
	$(SILENCER)touch $@

dafny_test_clean:
	@echo Removing test witnesses
	$(SILENCER)$(RM) -rf $(DAFNY_TEST_OUT_DIR)

dafny_test_force: dafny_test_clean
	$(SILENCER)$(MAKE) -$(MAKEFLAGS) dafny_test


DAFNY_TEST_WITNESS_GLOBAL:=$(DAFNY_TEST_OUT_DIR)/.last_test

dafny_test_global: $(DAFNY_TEST_WITNESS_GLOBAL)
# only saves time if it doesn't have to verify all the mentioned files
# and still has to verify / run the test dir files

$(DAFNY_TEST_WITNESS_GLOBAL): $(DAFNY_TEST_FILES) $(DAFNY_SRC_FILES)
	$(SILENCER)$(DAFNY_EXEC)  /vcsLoad:2.5  /compileTarget:go /compile:3 /compileVerbose:0 /noExterns /out:$(DAFNY_TEST_OUT_DIR)/global $(DAFNY_TEST_FILES) $(DAFNY_SRC_FILES) /runAllTests:1
	$(SILENCER)touch $@

dafny_test_global_clean:
	@echo Removing global test witness
	$(SILENCER)$(RM) -rf $(DAFNY_TEST_WITNESS_GLOBAL)

###################### DAFNY GENERAL ########################

dafny: dafny_verify dafny_translate dafny_test

dafny_clean: dafny_translate_clean dafny_test_clean dafny_verify_clean

###################### GO ########################

go:
	UNIMPLEMENTED


clean:  dafny_clean #go_clean

.PHONY: clean all dafny dafny_clean dafny_translate_clean dafny_verify dafny_verify_force dafny_verify_clean dafny_run dafny_test dafny_test_clean dafny_test_force


