NAME = trie_hard
TARGETS = libtrie_hard.rlib

CARGO_DEPS = criterion divan once_cell paste phf radix_trie rstest
VERUS_DEPS =
VERUS_FLAGS = --rlimit 50

include dep.mk
