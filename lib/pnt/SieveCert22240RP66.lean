/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 649–657 of 5066

File 66 of 387: the parts `rows22240R_649` … `rows22240R_657` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 97292 in units of a depth-4 test: row 53 columns 26–26, row 53 columns
27–27, row 53 columns 28–28, row 53 columns 29–29, row 53 columns 30–30, row 53 columns 31–31, row 53 columns 32–32,
row 53 columns 33–33, row 53 columns 34–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_649 : rowsJ2 53 54 26 27 ≤ 168097241898 := by decide +kernel

theorem rows22240R_650 : rowsJ2 53 54 27 28 ≤ 146691657119 := by decide +kernel

theorem rows22240R_651 : rowsJ2 53 54 28 29 ≤ 127786276651 := by decide +kernel

theorem rows22240R_652 : rowsJ2 53 54 29 30 ≤ 110564143302 := by decide +kernel

theorem rows22240R_653 : rowsJ2 53 54 30 31 ≤ 89631820440 := by decide +kernel

theorem rows22240R_654 : rowsJ2 53 54 31 32 ≤ 71433795679 := by decide +kernel

theorem rows22240R_655 : rowsJ2 53 54 32 33 ≤ 53382181317 := by decide +kernel

theorem rows22240R_656 : rowsJ2 53 54 33 34 ≤ 39745226127 := by decide +kernel

theorem rows22240R_657 : rowsJ2 53 54 34 35 ≤ 26198591758 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_649
#print axioms SieveCert.rows22240R_657
