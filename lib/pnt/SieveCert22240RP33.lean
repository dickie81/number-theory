/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 366–375 of 5066

File 33 of 387: the parts `rows22240R_366` … `rows22240R_375` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 94672 in units of a depth-4 test: row 43 columns 22–23, row 43 columns
24–25, row 43 columns 26–26, row 43 columns 27–27, row 43 columns 28–28, row 43 columns 29–29, row 43 columns 30–30,
row 43 columns 31–31, row 43 columns 32–32, row 43 columns 33–33), each a sum of refined costs (`rows2` or `rowsJ2`)
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

theorem rows22240R_366 : rowsJ2 43 44 22 24 ≤ 1608777591260 := by decide +kernel

theorem rows22240R_367 : rowsJ2 43 44 24 26 ≤ 1350597582490 := by decide +kernel

theorem rows22240R_368 : rowsJ2 43 44 26 27 ≤ 583305138406 := by decide +kernel

theorem rows22240R_369 : rowsJ2 43 44 27 28 ≤ 531118331004 := by decide +kernel

theorem rows22240R_370 : rowsJ2 43 44 28 29 ≤ 485733068588 := by decide +kernel

theorem rows22240R_371 : rowsJ2 43 44 29 30 ≤ 455132685386 := by decide +kernel

theorem rows22240R_372 : rowsJ2 43 44 30 31 ≤ 439028009166 := by decide +kernel

theorem rows22240R_373 : rowsJ2 43 44 31 32 ≤ 444133395314 := by decide +kernel

theorem rows22240R_374 : rowsJ2 43 44 32 33 ≤ 436552170018 := by decide +kernel

theorem rows22240R_375 : rowsJ2 43 44 33 34 ≤ 416280317387 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_366
#print axioms SieveCert.rows22240R_375
