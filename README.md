# Verified Trie-Hard

This repo is an attempt to formally verify the [trie-hard](https://github.com/cloudflare/trie-hard) project
using the [Verus](https://github.com/verus-lang/verus) program verifier.

To verify and build this project, first install a wrapper around cargo that enables Verus:
```
VERUS_COMMIT=0eedcf0 cargo install --git https://github.com/zhengyao-lin/vargo.git vargo
```

A command `vargo` with similar usage to `cargo` will be available.
To verify and build:
```
vargo build [--release]
```

## Building without Verification

If Verus somehow does not work, you can also run `cargo` directly to compile without verification:
```
cargo build [--release]
```
