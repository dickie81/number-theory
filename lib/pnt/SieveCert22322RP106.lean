/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 406–409 of 561

File 106 of 143: the parts `rows22322R_406` … `rows22322R_409` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 26444 tests: row 115 columns 61–68, row 115 columns 69–299, row 116 columns
0–48, row 116 columns 49–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_406 : rowsJ2 115 116 61 69 ≤ 13529506065588 := by decide +kernel

theorem rows22322R_407 : rowsJ2 115 116 69 300 ≤ 209834007233 := by decide +kernel

theorem rows22322R_408 : rowsJ2 116 117 0 49 ≤ 230070227072896 := by decide +kernel

theorem rows22322R_409 : rowsJ2 116 117 49 55 ≤ 63485553613091 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_406
#print axioms SieveCert.rows22322R_409
