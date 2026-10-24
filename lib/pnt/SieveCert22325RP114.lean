/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 440–443 of 561

File 114 of 142: the parts `rows22325R_440` … `rows22325R_443` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 26647 tests: row 123 columns 47–53, row 123 columns 54–62, row 123 columns
63–299, row 124 columns 0–46), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_440 : rowsJ2 123 124 47 54 ≤ 91576951274322 := by decide +kernel

theorem rows22325R_441 : rowsJ2 123 124 54 63 ≤ 41922409078394 := by decide +kernel

theorem rows22325R_442 : rowsJ2 123 124 63 300 ≤ 1063566208193645 := by decide +kernel

theorem rows22325R_443 : rowsJ2 124 125 0 47 ≤ 164342190873813 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_440
#print axioms SieveCert.rows22325R_443
