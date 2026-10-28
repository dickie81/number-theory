/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 381–387 of 5066

File 35 of 387: the parts `rows22240R_381` … `rows22240R_387` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 97119 in units of a depth-4 test: row 43 columns 39–39, row 43 columns
40–40, row 43 columns 41–41, row 43 columns 42–42, row 43 columns 43–339, row 44 columns 0–13, row 44 columns
14–16), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_381 : rowsJ2 43 44 39 40 ≤ 186063690577 := by decide +kernel

theorem rows22240R_382 : rowsJ2 43 44 40 41 ≤ 154082808395 := by decide +kernel

theorem rows22240R_383 : rowsJ2 43 44 41 42 ≤ 127582703571 := by decide +kernel

theorem rows22240R_384 : rowsJ2 43 44 42 43 ≤ 101267152023 := by decide +kernel

theorem rows22240R_385 : rowsJ2 43 44 43 340 ≤ 80434348179 := by decide +kernel

theorem rows22240R_386 : rowsJ2 44 45 0 14 ≤ 1044875177771 := by decide +kernel

theorem rows22240R_387 : rowsJ2 44 45 14 17 ≤ 2169321461428 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_381
#print axioms SieveCert.rows22240R_387
