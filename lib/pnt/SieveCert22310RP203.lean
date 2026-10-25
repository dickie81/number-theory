/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 810–813 of 1732

File 203 of 430: the parts `rows22310R_810` … `rows22310R_813` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24633 tests: row 122 columns 91–92, row 122 columns 93–94, row 122 columns
95–96, row 122 columns 97–99), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_810 : rowsJ2 122 123 91 93 ≤ 331573703573 := by decide +kernel

theorem rows22310R_811 : rowsJ2 122 123 93 95 ≤ 208886660057 := by decide +kernel

theorem rows22310R_812 : rowsJ2 122 123 95 97 ≤ 113344165024 := by decide +kernel

theorem rows22310R_813 : rowsJ2 122 123 97 100 ≤ 53683978210 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_810
#print axioms SieveCert.rows22310R_813
