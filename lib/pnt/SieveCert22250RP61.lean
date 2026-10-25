/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 570–581 of 5796

File 61 of 465: the parts `rows22250R_570` … `rows22250R_581` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 93419 tests: row 50 columns 49–49, row 50 columns 50–359, row 51 columns
0–14, row 51 columns 15–18, row 51 columns 19–21, row 51 columns 22–23, row 51 columns 24–25, row 51 columns 26–26,
row 51 columns 27–27, row 51 columns 28–28, row 51 columns 29–29, row 51 columns 30–30), each a sum of refined costs
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

theorem rows22250R_570 : rowsJ2 50 51 49 50 ≤ 1033270973399 := by decide +kernel

theorem rows22250R_571 : rowsJ2 50 51 50 360 ≤ 1553811116962 := by decide +kernel

theorem rows22250R_572 : rowsJ2 51 52 0 15 ≤ 1851415508740 := by decide +kernel

theorem rows22250R_573 : rowsJ2 51 52 15 19 ≤ 1941026075408 := by decide +kernel

theorem rows22250R_574 : rowsJ2 51 52 19 22 ≤ 1157000731927 := by decide +kernel

theorem rows22250R_575 : rowsJ2 51 52 22 24 ≤ 576143838954 := by decide +kernel

theorem rows22250R_576 : rowsJ2 51 52 24 26 ≤ 444417833024 := by decide +kernel

theorem rows22250R_577 : rowsJ2 51 52 26 27 ≤ 178855456514 := by decide +kernel

theorem rows22250R_578 : rowsJ2 51 52 27 28 ≤ 154908360138 := by decide +kernel

theorem rows22250R_579 : rowsJ2 51 52 28 29 ≤ 134333586271 := by decide +kernel

theorem rows22250R_580 : rowsJ2 51 52 29 30 ≤ 123509377459 := by decide +kernel

theorem rows22250R_581 : rowsJ2 51 52 30 31 ≤ 115523940319 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_570
#print axioms SieveCert.rows22250R_581
