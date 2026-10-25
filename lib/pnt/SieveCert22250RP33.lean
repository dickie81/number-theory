/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 368–374 of 5796

File 33 of 465: the parts `rows22250R_368` … `rows22250R_374` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 94985 tests: row 43 columns 29–29, row 43 columns 30–30, row 43 columns
31–31, row 43 columns 32–32, row 43 columns 33–33, row 43 columns 34–34, row 43 columns 35–35), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_368 : rowsJ2 43 44 29 30 ≤ 348691331760 := by decide +kernel

theorem rows22250R_369 : rowsJ2 43 44 30 31 ≤ 326738613105 := by decide +kernel

theorem rows22250R_370 : rowsJ2 43 44 31 32 ≤ 319048981844 := by decide +kernel

theorem rows22250R_371 : rowsJ2 43 44 32 33 ≤ 331776055986 := by decide +kernel

theorem rows22250R_372 : rowsJ2 43 44 33 34 ≤ 345441712575 := by decide +kernel

theorem rows22250R_373 : rowsJ2 43 44 34 35 ≤ 339182282952 := by decide +kernel

theorem rows22250R_374 : rowsJ2 43 44 35 36 ≤ 325308118425 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_368
#print axioms SieveCert.rows22250R_374
