/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 291–294 of 561

File 76 of 142: the parts `rows22325R_291` … `rows22325R_294` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29563 tests: row 96 columns 0–52, row 96 columns 53–59, row 96 columns 60–64,
row 96 columns 65–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_291 : rowsJ2 96 97 0 53 ≤ 565540865121050 := by decide +kernel

theorem rows22325R_292 : rowsJ2 96 97 53 60 ≤ 0 := by decide +kernel

theorem rows22325R_293 : rowsJ2 96 97 60 65 ≤ 66355957737 := by decide +kernel

theorem rows22325R_294 : rowsJ2 96 97 65 70 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_291
#print axioms SieveCert.rows22325R_294
