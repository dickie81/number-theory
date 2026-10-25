/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 878–881 of 1732

File 220 of 430: the parts `rows22310R_878` … `rows22310R_881` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24953 tests: row 126 columns 82–84, row 126 columns 85–86, row 126 columns
87–88, row 126 columns 89–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_878 : rowsJ2 126 127 82 85 ≤ 0 := by decide +kernel

theorem rows22310R_879 : rowsJ2 126 127 85 87 ≤ 113117988461 := by decide +kernel

theorem rows22310R_880 : rowsJ2 126 127 87 89 ≤ 107454848484 := by decide +kernel

theorem rows22310R_881 : rowsJ2 126 127 89 91 ≤ 43488278820 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_878
#print axioms SieveCert.rows22310R_881
