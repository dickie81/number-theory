/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 209–212 of 561

File 55 of 143: the parts `rows22322R_209` … `rows22322R_212` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28000 tests: row 85 columns 39–61, row 85 columns 62–66, row 85 columns
67–70, row 85 columns 71–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_209 : rowsJ2 85 86 39 62 ≤ 264113590257015 := by decide +kernel

theorem rows22322R_210 : rowsJ2 85 86 62 67 ≤ 1588544737193 := by decide +kernel

theorem rows22322R_211 : rowsJ2 85 86 67 71 ≤ 7224394592232 := by decide +kernel

theorem rows22322R_212 : rowsJ2 85 86 71 75 ≤ 5830744321536 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_209
#print axioms SieveCert.rows22322R_212
