/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 412–415 of 561

File 107 of 142: the parts `rows22325R_412` … `rows22325R_415` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24715 tests: row 116 columns 71–299, row 117 columns 0–48, row 117 columns
49–54, row 117 columns 55–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_412 : rowsJ2 116 117 71 300 ≤ 0 := by decide +kernel

theorem rows22325R_413 : rowsJ2 117 118 0 49 ≤ 221624625832151 := by decide +kernel

theorem rows22325R_414 : rowsJ2 117 118 49 55 ≤ 66470076558718 := by decide +kernel

theorem rows22325R_415 : rowsJ2 117 118 55 62 ≤ 42854657976080 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_412
#print axioms SieveCert.rows22325R_415
