/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 83–86 of 561

File 21 of 143: the parts `rows22322R_83` … `rows22322R_86` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24509 tests: row 59 columns 0–34, row 59 columns 35–43, row 59 columns 44–55,
row 59 columns 56–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22322R_83 : rowsJ2 59 60 0 35 ≤ 1058316727289556 := by decide +kernel

theorem rows22322R_84 : rowsJ2 59 60 35 44 ≤ 468103134223971 := by decide +kernel

theorem rows22322R_85 : rowsJ2 59 60 44 56 ≤ 725593541021610 := by decide +kernel

theorem rows22322R_86 : rowsJ2 59 60 56 300 ≤ 174254201442055 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_83
#print axioms SieveCert.rows22322R_86
