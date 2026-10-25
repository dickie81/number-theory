/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1518–1524 of 5796

File 153 of 465: the parts `rows22250R_1518` … `rows22250R_1524` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 91749 tests: row 73 columns 53–53, row 73 columns 54–54, row 73 columns
55–55, row 73 columns 56–56, row 73 columns 57–57, row 73 columns 58–58, row 73 columns 59–59), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1518 : rowsJ2 73 74 53 54 ≤ 3332922894254 := by decide +kernel

theorem rows22250R_1519 : rowsJ2 73 74 54 55 ≤ 3883446608657 := by decide +kernel

theorem rows22250R_1520 : rowsJ2 73 74 55 56 ≤ 4449140854972 := by decide +kernel

theorem rows22250R_1521 : rowsJ2 73 74 56 57 ≤ 5042079738291 := by decide +kernel

theorem rows22250R_1522 : rowsJ2 73 74 57 58 ≤ 5542741991506 := by decide +kernel

theorem rows22250R_1523 : rowsJ2 73 74 58 59 ≤ 5856443463730 := by decide +kernel

theorem rows22250R_1524 : rowsJ2 73 74 59 60 ≤ 5830344632768 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1518
#print axioms SieveCert.rows22250R_1524
