##########################################################################
### Makefile to compile Verus project with external cargo dependencies ###
##########################################################################

# Uses these variables (for example):
#   NAME = Name of the crate (e.g. vpl, parser)
#   TARGETS = Target executable/library name (e.g. vpl, libparser.rlib), can have multiple targets
#   SOURCE = All source files used for monitoring changes (e.g. $(wildcard src/*.rs) $(wildcard src/*.pl))
#   CARGO_DEPS = Rust dependencies added with `cargo add` (e.g. peg clap thiserror tempfile)
#   CARGO_TEST_DEPS = Rust dependencies that are only built for testing
#   VERUS_DEPS = Verus dependency paths (e.g. vest). For each dep in VERUS_DEPS, we expect $(dep).rlib and $(dep).verusdata to exist
#   TEST_TARGETS = List of custom test targets

EXEC_MAIN = src/main.rs
LIB_MAIN = src/lib.rs

FIRST_TARGET = $(firstword $(TARGETS))

# Recursive wildcard from https://stackoverflow.com/questions/2483182/recursive-wildcards-in-gnu-make/18258352#18258352
rwildcard=$(foreach d,$(wildcard $(1:=/*)),$(call rwildcard,$d,$2) $(filter $(subst *,%,$2),$d))

SOURCE = $(call rwildcard,src,*.rs)
# Append sources of VERUS_DEPS to SOURCE
SOURCE += $(foreach dep,$(VERUS_DEPS),$(call rwildcard,../$(dep)/src,*.rs))

.PHONY: debug
debug: $(foreach target,$(TARGETS),target/debug/$(target))

.PHONY: release
release: $(foreach target,$(TARGETS),target/release/$(target))

# Build each dependency in CARGO_DEPS
.PHONY: rust-deps-%
rust-deps-%: $(foreach dep,$(CARGO_DEPS),force-target/%/lib$(dep).rlib)
	@mkdir -p target/$*

# Build each dependency in CARGO_TEST_DEPS
.PHONY: rust-deps-%
rust-test-deps-%: $(foreach dep,$(CARGO_TEST_DEPS),force-target/%/lib$(dep).rlib)
	@mkdir -p target/$*

# Bulid each dependency in VERUS_DEPS
.PHONY: verus-deps-%
verus-deps-%:
	@for dep in $(VERUS_DEPS); do \
		pushd ../$$dep; \
		echo "Building Verus dependency $$dep"; \
		rlib=target/$*/lib$$dep.rlib; \
		make $$rlib || (echo "Fail to compile dependency $$dep"; exit 1) && \
		if [ ! -f $$rlib ] || [ ! -f $$rlib.verusdata ]; then \
			echo "Cannot find external Verus library $$rlib (or $$rlib.verusdata)"; \
			exit 1; \
		fi && \
		popd; \
    done

# The main verus command to run for TARGET
# Should be used in a context where $* is bound to either "debug" or "release"
# Each dependency <dep> in CARGO_DEPS is mapped to verus argument --extern <dep>=target/<release/debug>/deps/lib<dep>-*.<rlib|dylib>
# Each dependency <dep> in VERUS_DEPS is mapped to verus argument
#     --extern <dep>=../<dep>/target/<release/debug>/lib<dep>.rlib
#     --import <dep>=../<dep>/target/<release/debug>/lib<dep>.rlib.verusdata
#
# The entry rs file is fixed: src/main.rs for executables, and src/lib.rs for libraries
VERUS_COMMAND = \
	CARGO_MANIFEST_DIR=$(shell pwd) CARGO=$(shell which cargo) \
	verus $(if $(filter %.rlib,$@),$(LIB_MAIN),$(EXEC_MAIN)) \
		--crate-name $(NAME) \
		$(if $(filter %.rlib,$@),--crate-type=lib,) \
		-L dependency=target/$*/deps \
		$(foreach dep,$(CARGO_DEPS),--extern $(dep)=$(firstword $(wildcard target/$*/deps/lib$(dep)-*.rlib) $(wildcard target/$*/deps/lib$(dep)-*.dylib))) \
		$(foreach dep,$(VERUS_DEPS),-L dependency=../$(dep)/target/$*/deps) \
		$(foreach dep,$(VERUS_DEPS),-L dependency=../$(dep)/target/$*) \
		$(foreach dep,$(VERUS_DEPS),--extern $(dep)=../$(dep)/target/$*/lib$(dep).rlib --import $(dep)=../$(dep)/target/$*/lib$(dep).rlib.verusdata) \
		--compile $(if $(filter release,$*),-C opt-level=3) \
		-o $@ --export $@.verusdata \
		$(VERUS_FLAGS)

# Generate one rule for each target
define TARGET_TEMPLATE
target/%/$(1): rust-deps-% verus-deps-% $$(SOURCE)
	$$(VERUS_COMMAND)
endef
$(foreach target,$(TARGETS),$(eval $(call TARGET_TEMPLATE,$(target))))

# Build a test binary
target/%/test-$(FIRST_TARGET): rust-test-deps-% rust-deps-% verus-deps-% $(SOURCE)
	$(VERUS_COMMAND) --test

.PHONY: test
test: target/debug/test-$(FIRST_TARGET) $(TEST_TARGETS)
	target/debug/test-$(FIRST_TARGET)

# Named this way to avoid overlapping with the main target
force-target/debug/lib%.rlib: Cargo.toml
	cargo build --package=$*

force-target/release/lib%.rlib: Cargo.toml
	cargo build --package=$* --release

.PHONY: clean
clean:
	cargo clean
