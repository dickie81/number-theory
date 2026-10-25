/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 87–90 of 561

File 22 of 143: the parts `rows22322R_87` … `rows22322R_90` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24188 tests: row 60 columns 0–34, row 60 columns 35–43, row 60 columns 44–56,
row 60 columns 57–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22322R_87 : rowsJ2 60 61 0 35 ≤ 1001604352935621 := by decide +kernel

theorem rows22322R_88 : rowsJ2 60 61 35 44 ≤ 481252038043346 := by decide +kernel

theorem rows22322R_89 : rowsJ2 60 61 44 57 ≤ 745683116329509 := by decide +kernel

theorem rows22322R_90 : rowsJ2 60 61 57 300 ≤ 157842595569434 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_87
#print axioms SieveCert.rows22322R_90
