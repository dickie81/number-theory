/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 439–450 of 4715

File 43 of 351: the parts `rows22250R_439` … `rows22250R_450` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 91550 tests: row 47 columns 0–14, row 47 columns 15–18, row 47 columns
19–21, row 47 columns 22–23, row 47 columns 24–24, row 47 columns 25–25, row 47 columns 26–26, row 47 columns 27–27,
row 47 columns 28–28, row 47 columns 29–29, row 47 columns 30–30, row 47 columns 31–31), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_439 : rowsJ2 47 48 0 15 ≤ 2641321348616 := by decide +kernel

theorem rows22250R_440 : rowsJ2 47 48 15 19 ≤ 2532321773642 := by decide +kernel

theorem rows22250R_441 : rowsJ2 47 48 19 22 ≤ 1451133012087 := by decide +kernel

theorem rows22250R_442 : rowsJ2 47 48 22 24 ≤ 712137877609 := by decide +kernel

theorem rows22250R_443 : rowsJ2 47 48 24 25 ≤ 291468070938 := by decide +kernel

theorem rows22250R_444 : rowsJ2 47 48 25 26 ≤ 252488256420 := by decide +kernel

theorem rows22250R_445 : rowsJ2 47 48 26 27 ≤ 222118567504 := by decide +kernel

theorem rows22250R_446 : rowsJ2 47 48 27 28 ≤ 194694575565 := by decide +kernel

theorem rows22250R_447 : rowsJ2 47 48 28 29 ≤ 184373835417 := by decide +kernel

theorem rows22250R_448 : rowsJ2 47 48 29 30 ≤ 171804295783 := by decide +kernel

theorem rows22250R_449 : rowsJ2 47 48 30 31 ≤ 153455014993 := by decide +kernel

theorem rows22250R_450 : rowsJ2 47 48 31 32 ≤ 131142702566 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_439
#print axioms SieveCert.rows22250R_450
