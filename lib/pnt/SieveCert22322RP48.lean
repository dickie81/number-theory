/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 183–186 of 561

File 48 of 143: the parts `rows22322R_183` … `rows22322R_186` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24097 tests: row 81 columns 68–71, row 81 columns 72–75, row 81 columns
76–79, row 81 columns 80–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_183 : rowsJ2 81 82 68 72 ≤ 11812185690320 := by decide +kernel

theorem rows22322R_184 : rowsJ2 81 82 72 76 ≤ 12474257131642 := by decide +kernel

theorem rows22322R_185 : rowsJ2 81 82 76 80 ≤ 10206337752912 := by decide +kernel

theorem rows22322R_186 : rowsJ2 81 82 80 300 ≤ 6073051691841 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_183
#print axioms SieveCert.rows22322R_186
