/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1526–1534 of 4715

File 134 of 351: the parts `rows22250R_1526` … `rows22250R_1534` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, work 92079 in units of a depth-4 test: row 74 columns 49–49, row 74 columns
50–50, row 74 columns 51–51, row 74 columns 52–52, row 74 columns 53–53, row 74 columns 54–54, row 74 columns 55–55,
row 74 columns 56–56, row 74 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1526 : rowsJ2 74 75 49 50 ≤ 2559207816929 := by decide +kernel

theorem rows22250R_1527 : rowsJ2 74 75 50 51 ≤ 3036283988640 := by decide +kernel

theorem rows22250R_1528 : rowsJ2 74 75 51 52 ≤ 3525769805629 := by decide +kernel

theorem rows22250R_1529 : rowsJ2 74 75 52 53 ≤ 3718884106321 := by decide +kernel

theorem rows22250R_1530 : rowsJ2 74 75 53 54 ≤ 3610510840124 := by decide +kernel

theorem rows22250R_1531 : rowsJ2 74 75 54 55 ≤ 3262281114407 := by decide +kernel

theorem rows22250R_1532 : rowsJ2 74 75 55 56 ≤ 2970950426227 := by decide +kernel

theorem rows22250R_1533 : rowsJ2 74 75 56 57 ≤ 2682684946844 := by decide +kernel

theorem rows22250R_1534 : rowsJ2 74 75 57 58 ≤ 2451281813117 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1526
#print axioms SieveCert.rows22250R_1534
