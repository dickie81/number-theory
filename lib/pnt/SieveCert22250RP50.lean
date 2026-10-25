/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 484–495 of 5796

File 50 of 465: the parts `rows22250R_484` … `rows22250R_495` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 97012 tests: row 47 columns 47–359, row 48 columns 0–13, row 48 columns
14–17, row 48 columns 18–20, row 48 columns 21–23, row 48 columns 24–25, row 48 columns 26–26, row 48 columns 27–27,
row 48 columns 28–28, row 48 columns 29–29, row 48 columns 30–30, row 48 columns 31–31), each a sum of refined costs
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

theorem rows22250R_484 : rowsJ2 47 48 47 360 ≤ 133791135373 := by decide +kernel

theorem rows22250R_485 : rowsJ2 48 49 0 14 ≤ 1169206349081 := by decide +kernel

theorem rows22250R_486 : rowsJ2 48 49 14 18 ≤ 2222804508911 := by decide +kernel

theorem rows22250R_487 : rowsJ2 48 49 18 21 ≤ 1624327006477 := by decide +kernel

theorem rows22250R_488 : rowsJ2 48 49 21 24 ≤ 1275075950179 := by decide +kernel

theorem rows22250R_489 : rowsJ2 48 49 24 26 ≤ 643026904848 := by decide +kernel

theorem rows22250R_490 : rowsJ2 48 49 26 27 ≤ 268080901533 := by decide +kernel

theorem rows22250R_491 : rowsJ2 48 49 27 28 ≤ 234506316507 := by decide +kernel

theorem rows22250R_492 : rowsJ2 48 49 28 29 ≤ 208971715049 := by decide +kernel

theorem rows22250R_493 : rowsJ2 48 49 29 30 ≤ 188863348227 := by decide +kernel

theorem rows22250R_494 : rowsJ2 48 49 30 31 ≤ 180551262833 := by decide +kernel

theorem rows22250R_495 : rowsJ2 48 49 31 32 ≤ 177339829262 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_484
#print axioms SieveCert.rows22250R_495
