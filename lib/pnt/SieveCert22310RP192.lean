/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 765–768 of 1732

File 192 of 430: the parts `rows22310R_765` … `rows22310R_768` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28926 tests: row 120 columns 49–73, row 120 columns 74–78, row 120 columns
79–82, row 120 columns 83–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_765 : rowsJ2 120 121 49 74 ≤ 173652758066587 := by decide +kernel

theorem rows22310R_766 : rowsJ2 120 121 74 79 ≤ 106359102824 := by decide +kernel

theorem rows22310R_767 : rowsJ2 120 121 79 83 ≤ 0 := by decide +kernel

theorem rows22310R_768 : rowsJ2 120 121 83 86 ≤ 29464750829 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_765
#print axioms SieveCert.rows22310R_768
