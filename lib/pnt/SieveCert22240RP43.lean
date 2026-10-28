/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 446–452 of 5066

File 43 of 387: the parts `rows22240R_446` … `rows22240R_452` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 97683 in units of a depth-4 test: row 46 columns 29–29, row 46 columns
30–30, row 46 columns 31–31, row 46 columns 32–32, row 46 columns 33–33, row 46 columns 34–34, row 46 columns
35–35), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_446 : rowsJ2 46 47 29 30 ≤ 324612819958 := by decide +kernel

theorem rows22240R_447 : rowsJ2 46 47 30 31 ≤ 319422760608 := by decide +kernel

theorem rows22240R_448 : rowsJ2 46 47 31 32 ≤ 300472389894 := by decide +kernel

theorem rows22240R_449 : rowsJ2 46 47 32 33 ≤ 278327237695 := by decide +kernel

theorem rows22240R_450 : rowsJ2 46 47 33 34 ≤ 245277346258 := by decide +kernel

theorem rows22240R_451 : rowsJ2 46 47 34 35 ≤ 216932903521 := by decide +kernel

theorem rows22240R_452 : rowsJ2 46 47 35 36 ≤ 182159024045 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_446
#print axioms SieveCert.rows22240R_452
