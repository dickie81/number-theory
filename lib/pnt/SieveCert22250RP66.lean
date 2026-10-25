/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 684–695 of 4715

File 66 of 351: the parts `rows22250R_684` … `rows22250R_695` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 91771 tests: row 54 columns 53–53, row 54 columns 54–339, row 55 columns
0–15, row 55 columns 16–20, row 55 columns 21–22, row 55 columns 23–23, row 55 columns 24–24, row 55 columns 25–25,
row 55 columns 26–26, row 55 columns 27–27, row 55 columns 28–28, row 55 columns 29–29), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_684 : rowsJ2 54 55 53 54 ≤ 8878335948973 := by decide +kernel

theorem rows22250R_685 : rowsJ2 54 55 54 340 ≤ 10579463185830 := by decide +kernel

theorem rows22250R_686 : rowsJ2 55 56 0 16 ≤ 2973232141398 := by decide +kernel

theorem rows22250R_687 : rowsJ2 55 56 16 21 ≤ 1141727590575 := by decide +kernel

theorem rows22250R_688 : rowsJ2 55 56 21 23 ≤ 248080961559 := by decide +kernel

theorem rows22250R_689 : rowsJ2 55 56 23 24 ≤ 90017064359 := by decide +kernel

theorem rows22250R_690 : rowsJ2 55 56 24 25 ≤ 71872202157 := by decide +kernel

theorem rows22250R_691 : rowsJ2 55 56 25 26 ≤ 55102740041 := by decide +kernel

theorem rows22250R_692 : rowsJ2 55 56 26 27 ≤ 43309579648 := by decide +kernel

theorem rows22250R_693 : rowsJ2 55 56 27 28 ≤ 29273233151 := by decide +kernel

theorem rows22250R_694 : rowsJ2 55 56 28 29 ≤ 19096370383 := by decide +kernel

theorem rows22250R_695 : rowsJ2 55 56 29 30 ≤ 9565517073 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_684
#print axioms SieveCert.rows22250R_695
