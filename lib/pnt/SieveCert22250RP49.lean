/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 499–507 of 4715

File 49 of 351: the parts `rows22250R_499` … `rows22250R_507` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 89407 tests: row 49 columns 25–25, row 49 columns 26–26, row 49 columns
27–27, row 49 columns 28–28, row 49 columns 29–29, row 49 columns 30–30, row 49 columns 31–31, row 49 columns 32–32,
row 49 columns 33–33), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_499 : rowsJ2 49 50 25 26 ≤ 186860810281 := by decide +kernel

theorem rows22250R_500 : rowsJ2 49 50 26 27 ≤ 163197319233 := by decide +kernel

theorem rows22250R_501 : rowsJ2 49 50 27 28 ≤ 142330605509 := by decide +kernel

theorem rows22250R_502 : rowsJ2 49 50 28 29 ≤ 130474437247 := by decide +kernel

theorem rows22250R_503 : rowsJ2 49 50 29 30 ≤ 114385221803 := by decide +kernel

theorem rows22250R_504 : rowsJ2 49 50 30 31 ≤ 95646790124 := by decide +kernel

theorem rows22250R_505 : rowsJ2 49 50 31 32 ≤ 75675408971 := by decide +kernel

theorem rows22250R_506 : rowsJ2 49 50 32 33 ≤ 58029655391 := by decide +kernel

theorem rows22250R_507 : rowsJ2 49 50 33 34 ≤ 41001559586 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_499
#print axioms SieveCert.rows22250R_507
