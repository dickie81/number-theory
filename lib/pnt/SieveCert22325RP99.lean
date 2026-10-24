/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 380–383 of 561

File 99 of 142: the parts `rows22325R_380` … `rows22325R_383` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29494 tests: row 110 columns 57–62, row 110 columns 63–69, row 110 columns
70–299, row 111 columns 0–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_380 : rowsJ2 110 111 57 63 ≤ 23225005683621 := by decide +kernel

theorem rows22325R_381 : rowsJ2 110 111 63 70 ≤ 2568431091827 := by decide +kernel

theorem rows22325R_382 : rowsJ2 110 111 70 300 ≤ 327507903129179 := by decide +kernel

theorem rows22325R_383 : rowsJ2 111 112 0 51 ≤ 296973643635677 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_380
#print axioms SieveCert.rows22325R_383
