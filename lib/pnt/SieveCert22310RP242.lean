/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 966–969 of 1732

File 242 of 430: the parts `rows22310R_966` … `rows22310R_969` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27048 tests: row 131 columns 91–93, row 131 columns 94–96, row 131 columns
97–99, row 131 columns 100–102), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_966 : rowsJ2 131 132 91 94 ≤ 0 := by decide +kernel

theorem rows22310R_967 : rowsJ2 131 132 94 97 ≤ 0 := by decide +kernel

theorem rows22310R_968 : rowsJ2 131 132 97 100 ≤ 0 := by decide +kernel

theorem rows22310R_969 : rowsJ2 131 132 100 103 ≤ 906921800040 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_966
#print axioms SieveCert.rows22310R_969
