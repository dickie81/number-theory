/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 513–518 of 561

File 132 of 143: the parts `rows22322R_513` … `rows22322R_518` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (6 parts, 29383 tests: row 149 columns 39–299, row 150 columns 0–38, row 150 columns
39–299, row 151 columns 0–38, row 151 columns 39–299, row 152 columns 0–84), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_513 : rowsJ2 149 150 39 300 ≤ 2995996963234557 := by decide +kernel

theorem rows22322R_514 : rowsJ2 150 151 0 39 ≤ 216779550503781 := by decide +kernel

theorem rows22322R_515 : rowsJ2 150 151 39 300 ≤ 2996297645637965 := by decide +kernel

theorem rows22322R_516 : rowsJ2 151 152 0 39 ≤ 227778073168907 := by decide +kernel

theorem rows22322R_517 : rowsJ2 151 152 39 300 ≤ 3006799103126662 := by decide +kernel

theorem rows22322R_518 : rowsJ2 152 153 0 85 ≤ 348938761335433 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_513
#print axioms SieveCert.rows22322R_518
