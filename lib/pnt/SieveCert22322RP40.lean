/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 151–154 of 561

File 40 of 143: the parts `rows22322R_151` … `rows22322R_154` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 22902 tests: row 76 columns 61–67, row 76 columns 68–71, row 76 columns
72–75, row 76 columns 76–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_151 : rowsJ2 76 77 61 68 ≤ 25467001128393 := by decide +kernel

theorem rows22322R_152 : rowsJ2 76 77 68 72 ≤ 12956580062447 := by decide +kernel

theorem rows22322R_153 : rowsJ2 76 77 72 76 ≤ 24898105420111 := by decide +kernel

theorem rows22322R_154 : rowsJ2 76 77 76 300 ≤ 5752330124614 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_151
#print axioms SieveCert.rows22322R_154
