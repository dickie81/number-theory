/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 241–244 of 561

File 63 of 143: the parts `rows22322R_241` … `rows22322R_244` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29862 tests: row 89 columns 51–61, row 89 columns 62–66, row 89 columns
67–70, row 89 columns 71–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_241 : rowsJ2 89 90 51 62 ≤ 6237297811873 := by decide +kernel

theorem rows22322R_242 : rowsJ2 89 90 62 67 ≤ 1534627256240 := by decide +kernel

theorem rows22322R_243 : rowsJ2 89 90 67 71 ≤ 3079313402485 := by decide +kernel

theorem rows22322R_244 : rowsJ2 89 90 71 76 ≤ 1518535826189 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_241
#print axioms SieveCert.rows22322R_244
