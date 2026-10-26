/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 155–158 of 561

File 41 of 143: the parts `rows22322R_155` … `rows22322R_158` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29053 tests: row 77 columns 0–34, row 77 columns 35–60, row 77 columns 61–67,
row 77 columns 68–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_155 : rowsJ2 77 78 0 35 ≤ 546791896801615 := by decide +kernel

theorem rows22322R_156 : rowsJ2 77 78 35 61 ≤ 758309560175326 := by decide +kernel

theorem rows22322R_157 : rowsJ2 77 78 61 68 ≤ 18754519944110 := by decide +kernel

theorem rows22322R_158 : rowsJ2 77 78 68 72 ≤ 12845268487634 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_155
#print axioms SieveCert.rows22322R_158
