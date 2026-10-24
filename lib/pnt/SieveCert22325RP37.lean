/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 140–143 of 561

File 37 of 142: the parts `rows22325R_140` … `rows22325R_143` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 26562 tests: row 74 columns 35–58, row 74 columns 59–67, row 74 columns
68–72, row 74 columns 73–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_140 : rowsJ2 74 75 35 59 ≤ 878599224033976 := by decide +kernel

theorem rows22325R_141 : rowsJ2 74 75 59 68 ≤ 65544284684342 := by decide +kernel

theorem rows22325R_142 : rowsJ2 74 75 68 73 ≤ 20093410821839 := by decide +kernel

theorem rows22325R_143 : rowsJ2 74 75 73 300 ≤ 15066517079970 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_140
#print axioms SieveCert.rows22325R_143
