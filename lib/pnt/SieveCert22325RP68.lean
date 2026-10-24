/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 261–263 of 561

File 68 of 142: the parts `rows22325R_261` … `rows22325R_263` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 23462 tests: row 91 columns 75–80, row 91 columns 81–299, row 92 columns
0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_261 : rowsJ2 91 92 75 81 ≤ 8646250605884 := by decide +kernel

theorem rows22325R_262 : rowsJ2 91 92 81 300 ≤ 629026672282278 := by decide +kernel

theorem rows22325R_263 : rowsJ2 92 93 0 53 ≤ 669923783844528 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_261
#print axioms SieveCert.rows22325R_263
