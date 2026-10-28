/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3435–3450 of 5066

File 277 of 387: the parts `rows22240R_3435` … `rows22240R_3450` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 98836 in units of a depth-4 test: row 119 columns 93–94, row 119
columns 95–339, row 120 columns 0–26, row 120 columns 27–29, row 120 columns 30–31, row 120 columns 32–33, row 120
columns 34–36, row 120 columns 37–41, row 120 columns 42–55, row 120 columns 56–59, row 120 columns 60–61, row 120
columns 62–63, row 120 columns 64–64, row 120 columns 65–65, row 120 columns 66–66, row 120 columns 67–67), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3435 : rowsJ2 119 120 93 95 ≤ 24481795544909 := by decide +kernel

theorem rows22240R_3436 : rowsJ2 119 120 95 340 ≤ 1327074811843443 := by decide +kernel

theorem rows22240R_3437 : rowsJ2 120 121 0 27 ≤ 2006885860886 := by decide +kernel

theorem rows22240R_3438 : rowsJ2 120 121 27 30 ≤ 12531237456157 := by decide +kernel

theorem rows22240R_3439 : rowsJ2 120 121 30 32 ≤ 17349932271246 := by decide +kernel

theorem rows22240R_3440 : rowsJ2 120 121 32 34 ≤ 16389421798513 := by decide +kernel

theorem rows22240R_3441 : rowsJ2 120 121 34 37 ≤ 17112362892573 := by decide +kernel

theorem rows22240R_3442 : rowsJ2 120 121 37 42 ≤ 10318516773852 := by decide +kernel

theorem rows22240R_3443 : rowsJ2 120 121 42 56 ≤ 533182692987 := by decide +kernel

theorem rows22240R_3444 : rowsJ2 120 121 56 60 ≤ 3569245892350 := by decide +kernel

theorem rows22240R_3445 : rowsJ2 120 121 60 62 ≤ 3926641845004 := by decide +kernel

theorem rows22240R_3446 : rowsJ2 120 121 62 64 ≤ 5356254650345 := by decide +kernel

theorem rows22240R_3447 : rowsJ2 120 121 64 65 ≤ 3065282139852 := by decide +kernel

theorem rows22240R_3448 : rowsJ2 120 121 65 66 ≤ 3233285643616 := by decide +kernel

theorem rows22240R_3449 : rowsJ2 120 121 66 67 ≤ 3349983509557 := by decide +kernel

theorem rows22240R_3450 : rowsJ2 120 121 67 68 ≤ 3391176582181 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3435
#print axioms SieveCert.rows22240R_3450
