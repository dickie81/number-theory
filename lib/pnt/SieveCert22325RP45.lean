/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 171–174 of 561

File 45 of 142: the parts `rows22325R_171` … `rows22325R_174` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29904 tests: row 79 columns 72–75, row 79 columns 76–299, row 80 columns
0–35, row 80 columns 36–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_171 : rowsJ2 79 80 72 76 ≤ 17351898928023 := by decide +kernel

theorem rows22325R_172 : rowsJ2 79 80 76 300 ≤ 13777935424641 := by decide +kernel

theorem rows22325R_173 : rowsJ2 80 81 0 36 ≤ 562583036799520 := by decide +kernel

theorem rows22325R_174 : rowsJ2 80 81 36 62 ≤ 568089295026850 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_171
#print axioms SieveCert.rows22325R_174
