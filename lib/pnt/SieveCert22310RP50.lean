/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 201–204 of 1732

File 50 of 430: the parts `rows22310R_201` … `rows22310R_204` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28131 tests: row 74 columns 44–49, row 74 columns 50–54, row 74 columns
55–58, row 74 columns 59–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_201 : rowsJ2 74 75 44 50 ≤ 89034362440005 := by decide +kernel

theorem rows22310R_202 : rowsJ2 74 75 50 55 ≤ 106980349889508 := by decide +kernel

theorem rows22310R_203 : rowsJ2 74 75 55 59 ≤ 130793229682617 := by decide +kernel

theorem rows22310R_204 : rowsJ2 74 75 59 63 ≤ 170352105206781 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_201
#print axioms SieveCert.rows22310R_204
