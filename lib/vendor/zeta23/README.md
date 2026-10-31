# zeta23 (vendored)

These are 117 files of the `zeta23` folder of `https://github.com/anthropics/formal-math` at commit
`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`. They are the files that the library's modules import, directly or
through each other. zeta23 is Copyright 2026 Anthropic, PBC, and is released under the Apache License 2.0, with the
notice in `NOTICE` and the license in `LICENSE`. Its files under `Zeta23/FromPNTPlus/` derive from
PrimeNumberTheoremAnd (Apache 2.0).

## The port

Upstream builds this commit with Lean v4.33.0-rc2 and Mathlib `51e6992e`. Here the files are ported to this
repository's toolchain (Lean v4.35.0-rc3, Mathlib `0f64d30a`) by `zeta23_port.patch`, whose header lists each change.
All the changes are forced by Mathlib's API changes between the two versions. Each patched file starts with a comment
saying that it was modified. The other files are upstream's, unchanged.

`python3 scripts/check_vendor.py` checks the port. It fetches the commit, applies the patch, and compares the result
with these files byte for byte.

`lakefile.lean` builds these files with `relaxedAutoImplicit` off.
