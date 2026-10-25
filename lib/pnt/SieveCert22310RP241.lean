/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 962–965 of 1732

File 241 of 430: the parts `rows22310R_962` … `rows22310R_965` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26835 tests: row 131 columns 81–83, row 131 columns 84–85, row 131 columns
86–87, row 131 columns 88–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_962 : rowsJ2 131 132 81 84 ≤ 0 := by decide +kernel

theorem rows22310R_963 : rowsJ2 131 132 84 86 ≤ 0 := by decide +kernel

theorem rows22310R_964 : rowsJ2 131 132 86 88 ≤ 0 := by decide +kernel

theorem rows22310R_965 : rowsJ2 131 132 88 91 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_962
#print axioms SieveCert.rows22310R_965
