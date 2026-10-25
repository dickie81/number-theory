/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 386–395 of 5796

File 36 of 465: the parts `rows22250R_386` … `rows22250R_395` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 92390 tests: row 44 columns 20–22, row 44 columns 23–24, row 44 columns
25–26, row 44 columns 27–27, row 44 columns 28–28, row 44 columns 29–29, row 44 columns 30–30, row 44 columns 31–31,
row 44 columns 32–32, row 44 columns 33–33), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_386 : rowsJ2 44 45 20 23 ≤ 1955056885282 := by decide +kernel

theorem rows22250R_387 : rowsJ2 44 45 23 25 ≤ 1075678113733 := by decide +kernel

theorem rows22250R_388 : rowsJ2 44 45 25 27 ≤ 883277502543 := by decide +kernel

theorem rows22250R_389 : rowsJ2 44 45 27 28 ≤ 375943400387 := by decide +kernel

theorem rows22250R_390 : rowsJ2 44 45 28 29 ≤ 340571680707 := by decide +kernel

theorem rows22250R_391 : rowsJ2 44 45 29 30 ≤ 310993154029 := by decide +kernel

theorem rows22250R_392 : rowsJ2 44 45 30 31 ≤ 293542440339 := by decide +kernel

theorem rows22250R_393 : rowsJ2 44 45 31 32 ≤ 285833593898 := by decide +kernel

theorem rows22250R_394 : rowsJ2 44 45 32 33 ≤ 302720261291 := by decide +kernel

theorem rows22250R_395 : rowsJ2 44 45 33 34 ≤ 300686775702 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_386
#print axioms SieveCert.rows22250R_395
