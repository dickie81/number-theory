/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2599–2610 of 5066

File 223 of 387: the parts `rows22240R_2599` … `rows22240R_2610` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 95412 in units of a depth-4 test: row 96 columns 71–75, row 96 columns
76–78, row 96 columns 79–79, row 96 columns 80–80, row 96 columns 81–81, row 96 columns 82–82, row 96 columns 83–83,
row 96 columns 84–84, row 96 columns 85–85, row 96 columns 86–86, row 96 columns 87–87, row 96 columns 88–88), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2599 : rowsJ2 96 97 71 76 ≤ 0 := by decide +kernel

theorem rows22240R_2600 : rowsJ2 96 97 76 79 ≤ 614210300377 := by decide +kernel

theorem rows22240R_2601 : rowsJ2 96 97 79 80 ≤ 625912930833 := by decide +kernel

theorem rows22240R_2602 : rowsJ2 96 97 80 81 ≤ 951488528537 := by decide +kernel

theorem rows22240R_2603 : rowsJ2 96 97 81 82 ≤ 1416909847897 := by decide +kernel

theorem rows22240R_2604 : rowsJ2 96 97 82 83 ≤ 2048365105871 := by decide +kernel

theorem rows22240R_2605 : rowsJ2 96 97 83 84 ≤ 2842229264787 := by decide +kernel

theorem rows22240R_2606 : rowsJ2 96 97 84 85 ≤ 3729532330215 := by decide +kernel

theorem rows22240R_2607 : rowsJ2 96 97 85 86 ≤ 4401102978387 := by decide +kernel

theorem rows22240R_2608 : rowsJ2 96 97 86 87 ≤ 3749113891647 := by decide +kernel

theorem rows22240R_2609 : rowsJ2 96 97 87 88 ≤ 3207652247459 := by decide +kernel

theorem rows22240R_2610 : rowsJ2 96 97 88 89 ≤ 3133450289216 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2599
#print axioms SieveCert.rows22240R_2610
