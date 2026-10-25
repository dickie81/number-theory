/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 20–23 of 561

File 5 of 143: the parts `rows22322R_20` … `rows22322R_23` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 23821 tests: row 39 columns 0–34, row 39 columns 35–299, row 40 columns 0–34,
row 40 columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22322R_20 : rowsJ2 39 40 0 35 ≤ 2528774057145229 := by decide +kernel

theorem rows22322R_21 : rowsJ2 39 40 35 300 ≤ 320804893102760 := by decide +kernel

theorem rows22322R_22 : rowsJ2 40 41 0 35 ≤ 2447797574070697 := by decide +kernel

theorem rows22322R_23 : rowsJ2 40 41 35 300 ≤ 356042701571067 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_20
#print axioms SieveCert.rows22322R_23
