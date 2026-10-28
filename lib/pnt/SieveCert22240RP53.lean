/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 527–533 of 5066

File 53 of 387: the parts `rows22240R_527` … `rows22240R_533` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 94211 in units of a depth-4 test: row 49 columns 29–29, row 49 columns
30–30, row 49 columns 31–31, row 49 columns 32–32, row 49 columns 33–33, row 49 columns 34–34, row 49 columns
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

theorem rows22240R_527 : rowsJ2 49 50 29 30 ≤ 223883495879 := by decide +kernel

theorem rows22240R_528 : rowsJ2 49 50 30 31 ≤ 201523896841 := by decide +kernel

theorem rows22240R_529 : rowsJ2 49 50 31 32 ≤ 179742435274 := by decide +kernel

theorem rows22240R_530 : rowsJ2 49 50 32 33 ≤ 151830358708 := by decide +kernel

theorem rows22240R_531 : rowsJ2 49 50 33 34 ≤ 129313293929 := by decide +kernel

theorem rows22240R_532 : rowsJ2 49 50 34 35 ≤ 105133153746 := by decide +kernel

theorem rows22240R_533 : rowsJ2 49 50 35 36 ≤ 84644726070 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_527
#print axioms SieveCert.rows22240R_533
