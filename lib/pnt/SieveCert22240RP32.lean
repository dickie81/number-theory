/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 358–365 of 5066

File 32 of 387: the parts `rows22240R_358` … `rows22240R_365` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (8 parts, work 97978 in units of a depth-4 test: row 42 columns 39–39, row 42 columns
40–40, row 42 columns 41–41, row 42 columns 42–339, row 43 columns 0–13, row 43 columns 14–16, row 43 columns 17–19,
row 43 columns 20–21), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

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

theorem rows22240R_358 : rowsJ2 42 43 39 40 ≤ 245458748295 := by decide +kernel

theorem rows22240R_359 : rowsJ2 42 43 40 41 ≤ 213301438483 := by decide +kernel

theorem rows22240R_360 : rowsJ2 42 43 41 42 ≤ 176817009584 := by decide +kernel

theorem rows22240R_361 : rowsJ2 42 43 42 340 ≤ 150384513593 := by decide +kernel

theorem rows22240R_362 : rowsJ2 43 44 0 14 ≤ 948401751618 := by decide +kernel

theorem rows22240R_363 : rowsJ2 43 44 14 17 ≤ 2155610146112 := by decide +kernel

theorem rows22240R_364 : rowsJ2 43 44 17 20 ≤ 2785877305498 := by decide +kernel

theorem rows22240R_365 : rowsJ2 43 44 20 22 ≤ 1811487090974 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_358
#print axioms SieveCert.rows22240R_365
