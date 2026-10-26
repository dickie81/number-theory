/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 171–174 of 561

File 45 of 143: the parts `rows22322R_171` … `rows22322R_174` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29904 tests: row 79 columns 72–75, row 79 columns 76–299, row 80 columns
0–35, row 80 columns 36–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_171 : rowsJ2 79 80 72 76 ≤ 17391004909461 := by decide +kernel

theorem rows22322R_172 : rowsJ2 79 80 76 300 ≤ 13810541229414 := by decide +kernel

theorem rows22322R_173 : rowsJ2 80 81 0 36 ≤ 581878157264704 := by decide +kernel

theorem rows22322R_174 : rowsJ2 80 81 36 62 ≤ 570304355538599 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_171
#print axioms SieveCert.rows22322R_174
