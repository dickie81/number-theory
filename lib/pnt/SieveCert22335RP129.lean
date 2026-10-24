/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 501–507 of 549

File 129 of 140: the parts `rows22335R_501` … `rows22335R_507` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (7 parts, 29598 tests: row 149 columns 39–299, row 150 columns 0–38, row 150 columns
39–299, row 151 columns 0–38, row 151 columns 39–299, row 152 columns 0–87, row 152 columns 88–299), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_501 : rowsJ2 149 150 39 300 ≤ 2910639693494769 := by decide +kernel

theorem rows22335R_502 : rowsJ2 150 151 0 39 ≤ 213401954049288 := by decide +kernel

theorem rows22335R_503 : rowsJ2 150 151 39 300 ≤ 2913022246072176 := by decide +kernel

theorem rows22335R_504 : rowsJ2 151 152 0 39 ≤ 225011556337810 := by decide +kernel

theorem rows22335R_505 : rowsJ2 151 152 39 300 ≤ 2916261573070687 := by decide +kernel

theorem rows22335R_506 : rowsJ2 152 153 0 88 ≤ 655838772559202 := by decide +kernel

theorem rows22335R_507 : rowsJ2 152 153 88 300 ≤ 2499750957247992 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_501
#print axioms SieveCert.rows22335R_507
