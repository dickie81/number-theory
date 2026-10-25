/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 411–422 of 4715

File 40 of 351: the parts `rows22250R_411` … `rows22250R_422` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 88135 tests: row 45 columns 45–339, row 46 columns 0–14, row 46 columns
15–18, row 46 columns 19–21, row 46 columns 22–23, row 46 columns 24–24, row 46 columns 25–25, row 46 columns 26–26,
row 46 columns 27–27, row 46 columns 28–28, row 46 columns 29–29, row 46 columns 30–30), each a sum of refined costs
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

theorem rows22250R_411 : rowsJ2 45 46 45 340 ≤ 319798179595 := by decide +kernel

theorem rows22250R_412 : rowsJ2 46 47 0 15 ≤ 2576250154280 := by decide +kernel

theorem rows22250R_413 : rowsJ2 46 47 15 19 ≤ 2705659317713 := by decide +kernel

theorem rows22250R_414 : rowsJ2 46 47 19 22 ≤ 1614694464593 := by decide +kernel

theorem rows22250R_415 : rowsJ2 46 47 22 24 ≤ 804973417250 := by decide +kernel

theorem rows22250R_416 : rowsJ2 46 47 24 25 ≤ 331108695680 := by decide +kernel

theorem rows22250R_417 : rowsJ2 46 47 25 26 ≤ 291821485047 := by decide +kernel

theorem rows22250R_418 : rowsJ2 46 47 26 27 ≤ 254967491876 := by decide +kernel

theorem rows22250R_419 : rowsJ2 46 47 27 28 ≤ 227369697915 := by decide +kernel

theorem rows22250R_420 : rowsJ2 46 47 28 29 ≤ 210733158624 := by decide +kernel

theorem rows22250R_421 : rowsJ2 46 47 29 30 ≤ 206212996324 := by decide +kernel

theorem rows22250R_422 : rowsJ2 46 47 30 31 ≤ 191981891945 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_411
#print axioms SieveCert.rows22250R_422
