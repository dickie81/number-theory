/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 666–677 of 5796

File 72 of 465: the parts `rows22250R_666` … `rows22250R_677` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 94972 tests: row 53 columns 52–52, row 53 columns 53–359, row 54 columns
0–14, row 54 columns 15–19, row 54 columns 20–22, row 54 columns 23–24, row 54 columns 25–25, row 54 columns 26–26,
row 54 columns 27–27, row 54 columns 28–28, row 54 columns 29–29, row 54 columns 30–30), each a sum of refined costs
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

theorem rows22250R_666 : rowsJ2 53 54 52 53 ≤ 3111072450379 := by decide +kernel

theorem rows22250R_667 : rowsJ2 53 54 53 360 ≤ 4075749786527 := by decide +kernel

theorem rows22250R_668 : rowsJ2 54 55 0 15 ≤ 1957572147818 := by decide +kernel

theorem rows22250R_669 : rowsJ2 54 55 15 20 ≤ 1869228359750 := by decide +kernel

theorem rows22250R_670 : rowsJ2 54 55 20 23 ≤ 724038806308 := by decide +kernel

theorem rows22250R_671 : rowsJ2 54 55 23 25 ≤ 337390060067 := by decide +kernel

theorem rows22250R_672 : rowsJ2 54 55 25 26 ≤ 132534449150 := by decide +kernel

theorem rows22250R_673 : rowsJ2 54 55 26 27 ≤ 113383788397 := by decide +kernel

theorem rows22250R_674 : rowsJ2 54 55 27 28 ≤ 94431859585 := by decide +kernel

theorem rows22250R_675 : rowsJ2 54 55 28 29 ≤ 81607374826 := by decide +kernel

theorem rows22250R_676 : rowsJ2 54 55 29 30 ≤ 71147907013 := by decide +kernel

theorem rows22250R_677 : rowsJ2 54 55 30 31 ≤ 60401920278 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_666
#print axioms SieveCert.rows22250R_677
