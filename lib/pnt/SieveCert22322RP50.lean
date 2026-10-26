/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 190–193 of 561

File 50 of 143: the parts `rows22322R_190` … `rows22322R_193` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 25296 tests: row 82 columns 68–71, row 82 columns 72–75, row 82 columns
76–79, row 82 columns 80–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_190 : rowsJ2 82 83 68 72 ≤ 11157944506629 := by decide +kernel

theorem rows22322R_191 : rowsJ2 82 83 72 76 ≤ 10335741557586 := by decide +kernel

theorem rows22322R_192 : rowsJ2 82 83 76 80 ≤ 8680315440133 := by decide +kernel

theorem rows22322R_193 : rowsJ2 82 83 80 300 ≤ 9237392203333 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_190
#print axioms SieveCert.rows22322R_193
