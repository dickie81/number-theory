/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 259–269 of 4715

File 21 of 351: the parts `rows22250R_259` … `rows22250R_269` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 98920 tests: row 39 columns 20–22, row 39 columns 23–24, row 39 columns
25–25, row 39 columns 26–26, row 39 columns 27–27, row 39 columns 28–28, row 39 columns 29–29, row 39 columns 30–30,
row 39 columns 31–31, row 39 columns 32–32, row 39 columns 33–33), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_259 : rowsJ2 39 40 20 23 ≤ 2728575880389 := by decide +kernel

theorem rows22250R_260 : rowsJ2 39 40 23 25 ≤ 1502879510967 := by decide +kernel

theorem rows22250R_261 : rowsJ2 39 40 25 26 ≤ 649667171985 := by decide +kernel

theorem rows22250R_262 : rowsJ2 39 40 26 27 ≤ 591625235461 := by decide +kernel

theorem rows22250R_263 : rowsJ2 39 40 27 28 ≤ 537226209799 := by decide +kernel

theorem rows22250R_264 : rowsJ2 39 40 28 29 ≤ 501033343700 := by decide +kernel

theorem rows22250R_265 : rowsJ2 39 40 29 30 ≤ 480086664843 := by decide +kernel

theorem rows22250R_266 : rowsJ2 39 40 30 31 ≤ 488172514387 := by decide +kernel

theorem rows22250R_267 : rowsJ2 39 40 31 32 ≤ 522423502181 := by decide +kernel

theorem rows22250R_268 : rowsJ2 39 40 32 33 ≤ 543096471856 := by decide +kernel

theorem rows22250R_269 : rowsJ2 39 40 33 34 ≤ 535074889907 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_259
#print axioms SieveCert.rows22250R_269
