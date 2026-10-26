/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 414–417 of 561

File 108 of 143: the parts `rows22322R_414` … `rows22322R_417` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 23637 tests: row 117 columns 49–54, row 117 columns 55–61, row 117 columns
62–71, row 117 columns 72–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_414 : rowsJ2 117 118 49 55 ≤ 66654528291203 := by decide +kernel

theorem rows22322R_415 : rowsJ2 117 118 55 62 ≤ 42972473487623 := by decide +kernel

theorem rows22322R_416 : rowsJ2 117 118 62 72 ≤ 9523335534066 := by decide +kernel

theorem rows22322R_417 : rowsJ2 117 118 72 300 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_414
#print axioms SieveCert.rows22322R_417
