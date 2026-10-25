/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 221–224 of 561

File 58 of 143: the parts `rows22322R_221` … `rows22322R_224` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24585 tests: row 86 columns 75–79, row 86 columns 80–85, row 86 columns
86–299, row 87 columns 0–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_221 : rowsJ2 86 87 75 80 ≤ 5767951160368 := by decide +kernel

theorem rows22322R_222 : rowsJ2 86 87 80 86 ≤ 27166134901355 := by decide +kernel

theorem rows22322R_223 : rowsJ2 86 87 86 300 ≤ 8512871059929 := by decide +kernel

theorem rows22322R_224 : rowsJ2 87 88 0 43 ≤ 728953649156395 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_221
#print axioms SieveCert.rows22322R_224
