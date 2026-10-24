/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 448–451 of 561

File 116 of 142: the parts `rows22325R_448` … `rows22325R_451` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 25099 tests: row 125 columns 46–52, row 125 columns 53–61, row 125 columns
62–299, row 126 columns 0–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_448 : rowsJ2 125 126 46 53 ≤ 95751229709175 := by decide +kernel

theorem rows22325R_449 : rowsJ2 125 126 53 62 ≤ 43465875296493 := by decide +kernel

theorem rows22325R_450 : rowsJ2 125 126 62 300 ≤ 1420752842269828 := by decide +kernel

theorem rows22325R_451 : rowsJ2 126 127 0 46 ≤ 148698905604185 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_448
#print axioms SieveCert.rows22325R_451
