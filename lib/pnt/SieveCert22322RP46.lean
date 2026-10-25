/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 175–178 of 561

File 46 of 143: the parts `rows22322R_175` … `rows22322R_178` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28444 tests: row 80 columns 62–67, row 80 columns 68–71, row 80 columns
72–75, row 80 columns 76–79), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_175 : rowsJ2 80 81 62 68 ≤ 4282859518077 := by decide +kernel

theorem rows22322R_176 : rowsJ2 80 81 68 72 ≤ 12520436159990 := by decide +kernel

theorem rows22322R_177 : rowsJ2 80 81 72 76 ≤ 14824668767442 := by decide +kernel

theorem rows22322R_178 : rowsJ2 80 81 76 80 ≤ 11836922779600 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_175
#print axioms SieveCert.rows22322R_178
