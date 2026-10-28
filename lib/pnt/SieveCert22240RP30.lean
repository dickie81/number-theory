/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 342–352 of 5066

File 30 of 387: the parts `rows22240R_342` … `rows22240R_352` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 99296 in units of a depth-4 test: row 42 columns 20–21, row 42 columns
22–23, row 42 columns 24–25, row 42 columns 26–26, row 42 columns 27–27, row 42 columns 28–28, row 42 columns 29–29,
row 42 columns 30–30, row 42 columns 31–31, row 42 columns 32–32, row 42 columns 33–33), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_342 : rowsJ2 42 43 20 22 ≤ 1934453318369 := by decide +kernel

theorem rows22240R_343 : rowsJ2 42 43 22 24 ≤ 1741220124843 := by decide +kernel

theorem rows22240R_344 : rowsJ2 42 43 24 26 ≤ 1481726837038 := by decide +kernel

theorem rows22240R_345 : rowsJ2 42 43 26 27 ≤ 643053869122 := by decide +kernel

theorem rows22240R_346 : rowsJ2 42 43 27 28 ≤ 584987639073 := by decide +kernel

theorem rows22240R_347 : rowsJ2 42 43 28 29 ≤ 539202522237 := by decide +kernel

theorem rows22240R_348 : rowsJ2 42 43 29 30 ≤ 502955689734 := by decide +kernel

theorem rows22240R_349 : rowsJ2 42 43 30 31 ≤ 486801808519 := by decide +kernel

theorem rows22240R_350 : rowsJ2 42 43 31 32 ≤ 486638538706 := by decide +kernel

theorem rows22240R_351 : rowsJ2 42 43 32 33 ≤ 500348971701 := by decide +kernel

theorem rows22240R_352 : rowsJ2 42 43 33 34 ≤ 485120647245 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_342
#print axioms SieveCert.rows22240R_352
