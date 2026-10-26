/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 233–236 of 561

File 61 of 143: the parts `rows22322R_233` … `rows22322R_236` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29664 tests: row 88 columns 48–61, row 88 columns 62–66, row 88 columns
67–70, row 88 columns 71–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_233 : rowsJ2 88 89 48 62 ≤ 31263282908980 := by decide +kernel

theorem rows22322R_234 : rowsJ2 88 89 62 67 ≤ 1547680308447 := by decide +kernel

theorem rows22322R_235 : rowsJ2 88 89 67 71 ≤ 4239486992980 := by decide +kernel

theorem rows22322R_236 : rowsJ2 88 89 71 76 ≤ 2489135209599 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_233
#print axioms SieveCert.rows22322R_236
