/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 126–129 of 561

File 33 of 143: the parts `rows22322R_126` … `rows22322R_129` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28403 tests: row 71 columns 0–34, row 71 columns 35–50, row 71 columns 51–67,
row 71 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_126 : rowsJ2 71 72 0 35 ≤ 596510803222231 := by decide +kernel

theorem rows22322R_127 : rowsJ2 71 72 35 51 ≤ 805567522833007 := by decide +kernel

theorem rows22322R_128 : rowsJ2 71 72 51 68 ≤ 312716499062435 := by decide +kernel

theorem rows22322R_129 : rowsJ2 71 72 68 300 ≤ 23388559401549 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_126
#print axioms SieveCert.rows22322R_129
