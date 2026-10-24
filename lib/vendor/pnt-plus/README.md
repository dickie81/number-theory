# PrimeNumberTheoremAnd (vendored)

These are 19 files of PrimeNumberTheoremAnd (`https://github.com/AlexKontorovich/PrimeNumberTheoremAnd`) at commit
`650d31264be65f4cd6e70c45d8b25d86d482a761`. They are the files that the library's modules import, directly or
through each other. PrimeNumberTheoremAnd is by its contributors and is released under the Apache License 2.0, a
copy of which is in `LICENSE`.

## The port

Upstream builds this commit with Lean v4.33.1. Here the files are ported to this repository's toolchain (Lean
v4.35.0-rc3, Mathlib `0f64d30a`) by `pnt_port.patch`, whose header lists each change. All the changes are forced by
Mathlib's API changes between the two versions. Each patched file starts with a comment saying that it was modified.
The other files are upstream's, unchanged.

`python3 scripts/check_vendor.py` checks the port. It fetches the commit, applies the patch, and compares the result
with these files byte for byte.

## Lean options and the blueprint tool

- `lakefile.lean` builds these files with `autoImplicit` and `relaxedAutoImplicit` off.
- Upstream imports LeanArchitect (`https://github.com/hanwenzhu/LeanArchitect`, Apache 2.0) for its blueprint
  attributes. `lib/pnt/Architect.lean` is a stand-in for it: it accepts the same syntax and records nothing, so the
  attributes have no effect on any declaration.

## `sorry`

`Wiener.lean` has two lemmas proved by `sorry` (lines 329 and 349). No theorem checked by `lib/check/Check.lean`
depends on them: `scripts/check_axioms.py` fails if any of those theorems depends on `sorryAx`.
