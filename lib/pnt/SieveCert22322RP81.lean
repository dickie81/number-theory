/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 310–313 of 561

File 81 of 143: the parts `rows22322R_310` … `rows22322R_313` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24616 tests: row 98 columns 76–83, row 98 columns 84–299, row 99 columns
0–52, row 99 columns 53–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_310 : rowsJ2 98 99 76 84 ≤ 39905326639734 := by decide +kernel

theorem rows22322R_311 : rowsJ2 98 99 84 300 ≤ 956770295130731 := by decide +kernel

theorem rows22322R_312 : rowsJ2 99 100 0 53 ≤ 503098501961634 := by decide +kernel

theorem rows22322R_313 : rowsJ2 99 100 53 60 ≤ 1203942364856 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_310
#print axioms SieveCert.rows22322R_313
