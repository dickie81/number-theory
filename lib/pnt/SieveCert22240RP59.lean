/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 579–590 of 5066

File 59 of 387: the parts `rows22240R_579` … `rows22240R_590` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 92602 in units of a depth-4 test: row 51 columns 0–14, row 51 columns
15–18, row 51 columns 19–21, row 51 columns 22–23, row 51 columns 24–24, row 51 columns 25–25, row 51 columns 26–26,
row 51 columns 27–27, row 51 columns 28–28, row 51 columns 29–29, row 51 columns 30–30, row 51 columns 31–31), each
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

theorem rows22240R_579 : rowsJ2 51 52 0 15 ≤ 2337297063497 := by decide +kernel

theorem rows22240R_580 : rowsJ2 51 52 15 19 ≤ 2450431697164 := by decide +kernel

theorem rows22240R_581 : rowsJ2 51 52 19 22 ≤ 1461616872626 := by decide +kernel

theorem rows22240R_582 : rowsJ2 51 52 22 24 ≤ 728503523842 := by decide +kernel

theorem rows22240R_583 : rowsJ2 51 52 24 25 ≤ 299616655393 := by decide +kernel

theorem rows22240R_584 : rowsJ2 51 52 25 26 ≤ 262862966570 := by decide +kernel

theorem rows22240R_585 : rowsJ2 51 52 26 27 ≤ 227139939183 := by decide +kernel

theorem rows22240R_586 : rowsJ2 51 52 27 28 ≤ 199701231450 := by decide +kernel

theorem rows22240R_587 : rowsJ2 51 52 28 29 ≤ 178163874691 := by decide +kernel

theorem rows22240R_588 : rowsJ2 51 52 29 30 ≤ 160379370435 := by decide +kernel

theorem rows22240R_589 : rowsJ2 51 52 30 31 ≤ 136786164788 := by decide +kernel

theorem rows22240R_590 : rowsJ2 51 52 31 32 ≤ 114630196169 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_579
#print axioms SieveCert.rows22240R_590
