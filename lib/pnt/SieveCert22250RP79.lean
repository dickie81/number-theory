/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 733–744 of 5796

File 79 of 465: the parts `rows22250R_733` … `rows22250R_744` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 94679 tests: row 55 columns 52–52, row 55 columns 53–53, row 55 columns
54–54, row 55 columns 55–359, row 56 columns 0–14, row 56 columns 15–19, row 56 columns 20–22, row 56 columns 23–24,
row 56 columns 25–25, row 56 columns 26–26, row 56 columns 27–27, row 56 columns 28–28), each a sum of refined costs
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

theorem rows22250R_733 : rowsJ2 55 56 52 53 ≤ 3051700126764 := by decide +kernel

theorem rows22250R_734 : rowsJ2 55 56 53 54 ≤ 3997967369316 := by decide +kernel

theorem rows22250R_735 : rowsJ2 55 56 54 55 ≤ 4965513200768 := by decide +kernel

theorem rows22250R_736 : rowsJ2 55 56 55 360 ≤ 6131520286178 := by decide +kernel

theorem rows22250R_737 : rowsJ2 56 57 0 15 ≤ 1975921542305 := by decide +kernel

theorem rows22250R_738 : rowsJ2 56 57 15 20 ≤ 1541429248410 := by decide +kernel

theorem rows22250R_739 : rowsJ2 56 57 20 23 ≤ 552302514135 := by decide +kernel

theorem rows22250R_740 : rowsJ2 56 57 23 25 ≤ 247856428858 := by decide +kernel

theorem rows22250R_741 : rowsJ2 56 57 25 26 ≤ 95123964167 := by decide +kernel

theorem rows22250R_742 : rowsJ2 56 57 26 27 ≤ 79128822048 := by decide +kernel

theorem rows22250R_743 : rowsJ2 56 57 27 28 ≤ 63289347793 := by decide +kernel

theorem rows22250R_744 : rowsJ2 56 57 28 29 ≤ 53533126340 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_733
#print axioms SieveCert.rows22250R_744
