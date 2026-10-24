/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 190–193 of 561

File 50 of 142: the parts `rows22325R_190` … `rows22325R_193` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 25296 tests: row 82 columns 68–71, row 82 columns 72–75, row 82 columns
76–79, row 82 columns 80–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_190 : rowsJ2 82 83 68 72 ≤ 11133231110423 := by decide +kernel

theorem rows22325R_191 : rowsJ2 82 83 72 76 ≤ 10312196223897 := by decide +kernel

theorem rows22325R_192 : rowsJ2 82 83 76 80 ≤ 8658950031673 := by decide +kernel

theorem rows22325R_193 : rowsJ2 82 83 80 300 ≤ 9212101688486 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_190
#print axioms SieveCert.rows22325R_193
