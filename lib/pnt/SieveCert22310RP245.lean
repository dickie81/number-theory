/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 978–981 of 1732

File 245 of 430: the parts `rows22310R_978` … `rows22310R_981` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24126 tests: row 132 columns 81–82, row 132 columns 83–84, row 132 columns
85–86, row 132 columns 87–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_978 : rowsJ2 132 133 81 83 ≤ 0 := by decide +kernel

theorem rows22310R_979 : rowsJ2 132 133 83 85 ≤ 0 := by decide +kernel

theorem rows22310R_980 : rowsJ2 132 133 85 87 ≤ 0 := by decide +kernel

theorem rows22310R_981 : rowsJ2 132 133 87 90 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_978
#print axioms SieveCert.rows22310R_981
