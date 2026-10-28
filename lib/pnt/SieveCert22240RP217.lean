/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2521–2530 of 5066

File 217 of 387: the parts `rows22240R_2521` … `rows22240R_2530` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 93135 in units of a depth-4 test: row 94 columns 88–88, row 94 columns
89–89, row 94 columns 90–90, row 94 columns 91–91, row 94 columns 92–92, row 94 columns 93–93, row 94 columns
94–339, row 95 columns 0–15, row 95 columns 16–19, row 95 columns 20–25), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2521 : rowsJ2 94 95 88 89 ≤ 4347751427271 := by decide +kernel

theorem rows22240R_2522 : rowsJ2 94 95 89 90 ≤ 3862554609535 := by decide +kernel

theorem rows22240R_2523 : rowsJ2 94 95 90 91 ≤ 3844170667025 := by decide +kernel

theorem rows22240R_2524 : rowsJ2 94 95 91 92 ≤ 3898679527217 := by decide +kernel

theorem rows22240R_2525 : rowsJ2 94 95 92 93 ≤ 4045159013624 := by decide +kernel

theorem rows22240R_2526 : rowsJ2 94 95 93 94 ≤ 4268413211783 := by decide +kernel

theorem rows22240R_2527 : rowsJ2 94 95 94 340 ≤ 4588159887243 := by decide +kernel

theorem rows22240R_2528 : rowsJ2 95 96 0 16 ≤ 0 := by decide +kernel

theorem rows22240R_2529 : rowsJ2 95 96 16 20 ≤ 0 := by decide +kernel

theorem rows22240R_2530 : rowsJ2 95 96 20 26 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2521
#print axioms SieveCert.rows22240R_2530
