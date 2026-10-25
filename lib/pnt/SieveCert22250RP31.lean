/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 338–348 of 4715

File 31 of 351: the parts `rows22250R_338` … `rows22250R_348` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 93051 tests: row 42 columns 41–41, row 42 columns 42–339, row 43 columns
0–13, row 43 columns 14–17, row 43 columns 18–20, row 43 columns 21–23, row 43 columns 24–25, row 43 columns 26–26,
row 43 columns 27–27, row 43 columns 28–28, row 43 columns 29–29), each a sum of refined costs (`rows2` or `rowsJ2`)
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

theorem rows22250R_338 : rowsJ2 42 43 41 42 ≤ 72286614495 := by decide +kernel

theorem rows22250R_339 : rowsJ2 42 43 42 340 ≤ 56510869058 := by decide +kernel

theorem rows22250R_340 : rowsJ2 43 44 0 14 ≤ 1625359130923 := by decide +kernel

theorem rows22250R_341 : rowsJ2 43 44 14 18 ≤ 3095310402325 := by decide +kernel

theorem rows22250R_342 : rowsJ2 43 44 18 21 ≤ 2265630032861 := by decide +kernel

theorem rows22250R_343 : rowsJ2 43 44 21 24 ≤ 1780326029823 := by decide +kernel

theorem rows22250R_344 : rowsJ2 43 44 24 26 ≤ 900174106497 := by decide +kernel

theorem rows22250R_345 : rowsJ2 43 44 26 27 ≤ 379723441232 := by decide +kernel

theorem rows22250R_346 : rowsJ2 43 44 27 28 ≤ 339009842342 := by decide +kernel

theorem rows22250R_347 : rowsJ2 43 44 28 29 ≤ 315899220342 := by decide +kernel

theorem rows22250R_348 : rowsJ2 43 44 29 30 ≤ 307170037662 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_338
#print axioms SieveCert.rows22250R_348
