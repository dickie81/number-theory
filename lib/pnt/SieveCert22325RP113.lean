/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 436–439 of 561

File 113 of 142: the parts `rows22325R_436` … `rows22325R_439` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27437 tests: row 122 columns 47–53, row 122 columns 54–61, row 122 columns
62–299, row 123 columns 0–46), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_436 : rowsJ2 122 123 47 54 ≤ 90470642512777 := by decide +kernel

theorem rows22325R_437 : rowsJ2 122 123 54 62 ≤ 43661774272430 := by decide +kernel

theorem rows22325R_438 : rowsJ2 122 123 62 300 ≤ 881731488994904 := by decide +kernel

theorem rows22325R_439 : rowsJ2 123 124 0 47 ≤ 167583041874464 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_436
#print axioms SieveCert.rows22325R_439
