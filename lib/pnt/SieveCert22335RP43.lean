/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 163–166 of 549

File 43 of 140: the parts `rows22335R_163` … `rows22335R_166` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 26698 tests: row 78 columns 61–67, row 78 columns 68–71, row 78 columns
72–75, row 78 columns 76–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_163 : rowsJ2 78 79 61 68 ≤ 13224415407375 := by decide +kernel

theorem rows22335R_164 : rowsJ2 78 79 68 72 ≤ 12699262272767 := by decide +kernel

theorem rows22335R_165 : rowsJ2 78 79 72 76 ≤ 17487143534126 := by decide +kernel

theorem rows22335R_166 : rowsJ2 78 79 76 300 ≤ 10327192605400 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_163
#print axioms SieveCert.rows22335R_166
