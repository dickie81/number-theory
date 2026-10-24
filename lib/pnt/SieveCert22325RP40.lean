/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 151–154 of 561

File 40 of 142: the parts `rows22325R_151` … `rows22325R_154` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 22902 tests: row 76 columns 61–67, row 76 columns 68–71, row 76 columns
72–75, row 76 columns 76–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_151 : rowsJ2 76 77 61 68 ≤ 25364743773209 := by decide +kernel

theorem rows22325R_152 : rowsJ2 76 77 68 72 ≤ 12927065994448 := by decide +kernel

theorem rows22325R_153 : rowsJ2 76 77 72 76 ≤ 24842346213133 := by decide +kernel

theorem rows22325R_154 : rowsJ2 76 77 76 300 ≤ 5739210432670 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_151
#print axioms SieveCert.rows22325R_154
