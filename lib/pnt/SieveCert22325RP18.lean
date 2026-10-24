/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 71–74 of 561

File 18 of 142: the parts `rows22325R_71` … `rows22325R_74` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24904 tests: row 56 columns 0–34, row 56 columns 35–43, row 56 columns 44–52,
row 56 columns 53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_71 : rowsJ2 56 57 0 35 ≤ 1178929853633761 := by decide +kernel

theorem rows22325R_72 : rowsJ2 56 57 35 44 ≤ 412230873460466 := by decide +kernel

theorem rows22325R_73 : rowsJ2 56 57 44 53 ≤ 624096780013539 := by decide +kernel

theorem rows22325R_74 : rowsJ2 56 57 53 300 ≤ 224148900096027 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_71
#print axioms SieveCert.rows22325R_74
