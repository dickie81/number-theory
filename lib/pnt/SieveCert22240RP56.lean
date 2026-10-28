/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 552–561 of 5066

File 56 of 387: the parts `rows22240R_552` … `rows22240R_561` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 93862 in units of a depth-4 test: row 50 columns 24–24, row 50 columns
25–25, row 50 columns 26–26, row 50 columns 27–27, row 50 columns 28–28, row 50 columns 29–29, row 50 columns 30–30,
row 50 columns 31–31, row 50 columns 32–32, row 50 columns 33–33), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_552 : rowsJ2 50 51 24 25 ≤ 341151063677 := by decide +kernel

theorem rows22240R_553 : rowsJ2 50 51 25 26 ≤ 298491327107 := by decide +kernel

theorem rows22240R_554 : rowsJ2 50 51 26 27 ≤ 262506947822 := by decide +kernel

theorem rows22240R_555 : rowsJ2 50 51 27 28 ≤ 229228656479 := by decide +kernel

theorem rows22240R_556 : rowsJ2 50 51 28 29 ≤ 207583962357 := by decide +kernel

theorem rows22240R_557 : rowsJ2 50 51 29 30 ≤ 189218546883 := by decide +kernel

theorem rows22240R_558 : rowsJ2 50 51 30 31 ≤ 170262347727 := by decide +kernel

theorem rows22240R_559 : rowsJ2 50 51 31 32 ≤ 143879651241 := by decide +kernel

theorem rows22240R_560 : rowsJ2 50 51 32 33 ≤ 121939954296 := by decide +kernel

theorem rows22240R_561 : rowsJ2 50 51 33 34 ≤ 98307344128 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_552
#print axioms SieveCert.rows22240R_561
