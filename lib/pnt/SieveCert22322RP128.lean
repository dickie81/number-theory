/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 495–498 of 561

File 128 of 143: the parts `rows22322R_495` … `rows22322R_498` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29720 tests: row 140 columns 41–299, row 141 columns 0–40, row 141 columns
41–299, row 142 columns 0–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_495 : rowsJ2 140 141 41 300 ≤ 2987276850373881 := by decide +kernel

theorem rows22322R_496 : rowsJ2 141 142 0 41 ≤ 145326861870665 := by decide +kernel

theorem rows22322R_497 : rowsJ2 141 142 41 300 ≤ 2968370778932638 := by decide +kernel

theorem rows22322R_498 : rowsJ2 142 143 0 41 ≤ 158053942489364 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_495
#print axioms SieveCert.rows22322R_498
