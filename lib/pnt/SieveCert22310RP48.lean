/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 193–196 of 1732

File 48 of 430: the parts `rows22310R_193` … `rows22310R_196` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28062 tests: row 73 columns 50–54, row 73 columns 55–58, row 73 columns
59–62, row 73 columns 63–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_193 : rowsJ2 73 74 50 55 ≤ 105746472598463 := by decide +kernel

theorem rows22310R_194 : rowsJ2 73 74 55 59 ≤ 127119197368109 := by decide +kernel

theorem rows22310R_195 : rowsJ2 73 74 59 63 ≤ 169515339551542 := by decide +kernel

theorem rows22310R_196 : rowsJ2 73 74 63 67 ≤ 164554227957213 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_193
#print axioms SieveCert.rows22310R_196
