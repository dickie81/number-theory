/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 436–444 of 5796

File 43 of 465: the parts `rows22250R_436` … `rows22250R_444` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 84760 tests: row 46 columns 24–25, row 46 columns 26–26, row 46 columns
27–27, row 46 columns 28–28, row 46 columns 29–29, row 46 columns 30–30, row 46 columns 31–31, row 46 columns 32–32,
row 46 columns 33–33), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22250R_436 : rowsJ2 46 47 24 26 ≤ 799858030854 := by decide +kernel

theorem rows22250R_437 : rowsJ2 46 47 26 27 ≤ 338893501977 := by decide +kernel

theorem rows22250R_438 : rowsJ2 46 47 27 28 ≤ 300342982163 := by decide +kernel

theorem rows22250R_439 : rowsJ2 46 47 28 29 ≤ 269922210008 := by decide +kernel

theorem rows22250R_440 : rowsJ2 46 47 29 30 ≤ 245106411815 := by decide +kernel

theorem rows22250R_441 : rowsJ2 46 47 30 31 ≤ 232244616070 := by decide +kernel

theorem rows22250R_442 : rowsJ2 46 47 31 32 ≤ 228860650915 := by decide +kernel

theorem rows22250R_443 : rowsJ2 46 47 32 33 ≤ 234266843558 := by decide +kernel

theorem rows22250R_444 : rowsJ2 46 47 33 34 ≤ 222569199110 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_436
#print axioms SieveCert.rows22250R_444
