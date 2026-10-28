/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 469–476 of 5066

File 46 of 387: the parts `rows22240R_469` … `rows22240R_476` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (8 parts, work 84862 in units of a depth-4 test: row 47 columns 26–26, row 47 columns
27–27, row 47 columns 28–28, row 47 columns 29–29, row 47 columns 30–30, row 47 columns 31–31, row 47 columns 32–32,
row 47 columns 33–33), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_469 : rowsJ2 47 48 26 27 ≤ 380921001153 := by decide +kernel

theorem rows22240R_470 : rowsJ2 47 48 27 28 ≤ 341273946680 := by decide +kernel

theorem rows22240R_471 : rowsJ2 47 48 28 29 ≤ 307954422661 := by decide +kernel

theorem rows22240R_472 : rowsJ2 47 48 29 30 ≤ 288979621665 := by decide +kernel

theorem rows22240R_473 : rowsJ2 47 48 30 31 ≤ 276404652973 := by decide +kernel

theorem rows22240R_474 : rowsJ2 47 48 31 32 ≤ 255756016574 := by decide +kernel

theorem rows22240R_475 : rowsJ2 47 48 32 33 ≤ 226202638519 := by decide +kernel

theorem rows22240R_476 : rowsJ2 47 48 33 34 ≤ 198760667449 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_469
#print axioms SieveCert.rows22240R_476
