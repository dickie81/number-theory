/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 175–178 of 561

File 46 of 142: the parts `rows22325R_175` … `rows22325R_178` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28444 tests: row 80 columns 62–67, row 80 columns 68–71, row 80 columns
72–75, row 80 columns 76–79), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_175 : rowsJ2 80 81 62 68 ≤ 4270368489887 := by decide +kernel

theorem rows22325R_176 : rowsJ2 80 81 68 72 ≤ 12492544946973 := by decide +kernel

theorem rows22325R_177 : rowsJ2 80 81 72 76 ≤ 14791205497028 := by decide +kernel

theorem rows22325R_178 : rowsJ2 80 81 76 80 ≤ 11808674639317 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_175
#print axioms SieveCert.rows22325R_178
