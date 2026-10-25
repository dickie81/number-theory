/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 631–634 of 1732

File 159 of 430: the parts `rows22310R_631` … `rows22310R_634` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28911 tests: row 113 columns 35–44, row 113 columns 45–63, row 113 columns
64–78, row 113 columns 79–82), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_631 : rowsJ2 113 114 35 45 ≤ 228284293813553 := by decide +kernel

theorem rows22310R_632 : rowsJ2 113 114 45 64 ≤ 325452606307869 := by decide +kernel

theorem rows22310R_633 : rowsJ2 113 114 64 79 ≤ 69881862474651 := by decide +kernel

theorem rows22310R_634 : rowsJ2 113 114 79 83 ≤ 1029846732690 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_631
#print axioms SieveCert.rows22310R_634
