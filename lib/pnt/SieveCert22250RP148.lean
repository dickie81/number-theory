/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1463–1471 of 5796

File 148 of 465: the parts `rows22250R_1463` … `rows22250R_1471` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 89691 tests: row 72 columns 48–48, row 72 columns 49–49, row 72 columns
50–50, row 72 columns 51–51, row 72 columns 52–52, row 72 columns 53–53, row 72 columns 54–54, row 72 columns 55–55,
row 72 columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1463 : rowsJ2 72 73 48 49 ≤ 454431616772 := by decide +kernel

theorem rows22250R_1464 : rowsJ2 72 73 49 50 ≤ 846211035866 := by decide +kernel

theorem rows22250R_1465 : rowsJ2 72 73 50 51 ≤ 1272726412806 := by decide +kernel

theorem rows22250R_1466 : rowsJ2 72 73 51 52 ≤ 1832085480925 := by decide +kernel

theorem rows22250R_1467 : rowsJ2 72 73 52 53 ≤ 2625760574688 := by decide +kernel

theorem rows22250R_1468 : rowsJ2 72 73 53 54 ≤ 3400509422350 := by decide +kernel

theorem rows22250R_1469 : rowsJ2 72 73 54 55 ≤ 4037234179979 := by decide +kernel

theorem rows22250R_1470 : rowsJ2 72 73 55 56 ≤ 4650774183289 := by decide +kernel

theorem rows22250R_1471 : rowsJ2 72 73 56 57 ≤ 5333897259174 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1463
#print axioms SieveCert.rows22250R_1471
