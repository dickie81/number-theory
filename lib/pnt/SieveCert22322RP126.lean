/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 487–491 of 561

File 126 of 143: the parts `rows22322R_487` … `rows22322R_491` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (5 parts, 25424 tests: row 137 columns 42–51, row 137 columns 52–299, row 138 columns
0–41, row 138 columns 42–51, row 138 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_487 : rowsJ2 137 138 42 52 ≤ 128896714740122 := by decide +kernel

theorem rows22322R_488 : rowsJ2 137 138 52 300 ≤ 2872316499075886 := by decide +kernel

theorem rows22322R_489 : rowsJ2 138 139 0 42 ≤ 134670530774546 := by decide +kernel

theorem rows22322R_490 : rowsJ2 138 139 42 52 ≤ 124693575592108 := by decide +kernel

theorem rows22322R_491 : rowsJ2 138 139 52 300 ≤ 2859228617984202 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_487
#print axioms SieveCert.rows22322R_491
