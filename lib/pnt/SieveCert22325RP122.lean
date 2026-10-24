/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 471–474 of 561

File 122 of 142: the parts `rows22325R_471` … `rows22325R_474` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27652 tests: row 132 columns 0–43, row 132 columns 44–51, row 132 columns
52–299, row 133 columns 0–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_471 : rowsJ2 132 133 0 44 ≤ 129810685839751 := by decide +kernel

theorem rows22325R_472 : rowsJ2 132 133 44 52 ≤ 110565856187642 := by decide +kernel

theorem rows22325R_473 : rowsJ2 132 133 52 300 ≤ 2532644993814742 := by decide +kernel

theorem rows22325R_474 : rowsJ2 133 134 0 44 ≤ 135008909401548 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_471
#print axioms SieveCert.rows22325R_474
