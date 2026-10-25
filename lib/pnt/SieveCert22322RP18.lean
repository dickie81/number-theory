/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 71–74 of 561

File 18 of 143: the parts `rows22322R_71` … `rows22322R_74` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24904 tests: row 56 columns 0–34, row 56 columns 35–43, row 56 columns 44–52,
row 56 columns 53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22322R_71 : rowsJ2 56 57 0 35 ≤ 1242744726181156 := by decide +kernel

theorem rows22322R_72 : rowsJ2 56 57 35 44 ≤ 421135207900720 := by decide +kernel

theorem rows22322R_73 : rowsJ2 56 57 44 53 ≤ 626301360969655 := by decide +kernel

theorem rows22322R_74 : rowsJ2 56 57 53 300 ≤ 224957949271890 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_71
#print axioms SieveCert.rows22322R_74
