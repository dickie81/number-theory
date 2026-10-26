/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 133–135 of 561

File 35 of 143: the parts `rows22322R_133` … `rows22322R_135` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 23146 tests: row 72 columns 68–299, row 73 columns 0–34, row 73 columns
35–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_133 : rowsJ2 72 73 68 300 ≤ 25306112450310 := by decide +kernel

theorem rows22322R_134 : rowsJ2 73 74 0 35 ≤ 570199056614269 := by decide +kernel

theorem rows22322R_135 : rowsJ2 73 74 35 58 ≤ 912898104917375 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_133
#print axioms SieveCert.rows22322R_135
