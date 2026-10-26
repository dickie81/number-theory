/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 140–143 of 561

File 37 of 143: the parts `rows22322R_140` … `rows22322R_143` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 26562 tests: row 74 columns 35–58, row 74 columns 59–67, row 74 columns
68–72, row 74 columns 73–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_140 : rowsJ2 74 75 35 59 ≤ 881909619920157 := by decide +kernel

theorem rows22322R_141 : rowsJ2 74 75 59 68 ≤ 65812175864670 := by decide +kernel

theorem rows22322R_142 : rowsJ2 74 75 68 73 ≤ 20142073401282 := by decide +kernel

theorem rows22322R_143 : rowsJ2 74 75 73 300 ≤ 15100324314208 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_140
#print axioms SieveCert.rows22322R_143
