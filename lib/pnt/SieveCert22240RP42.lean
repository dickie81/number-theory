/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 434–445 of 5066

File 42 of 387: the parts `rows22240R_434` … `rows22240R_445` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 95921 in units of a depth-4 test: row 45 columns 43–43, row 45 columns
44–44, row 45 columns 45–339, row 46 columns 0–13, row 46 columns 14–17, row 46 columns 18–20, row 46 columns 21–22,
row 46 columns 23–24, row 46 columns 25–25, row 46 columns 26–26, row 46 columns 27–27, row 46 columns 28–28), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_434 : rowsJ2 45 46 43 44 ≤ 38170740736 := by decide +kernel

theorem rows22240R_435 : rowsJ2 45 46 44 45 ≤ 25203545195 := by decide +kernel

theorem rows22240R_436 : rowsJ2 45 46 45 340 ≤ 176176000328 := by decide +kernel

theorem rows22240R_437 : rowsJ2 46 47 0 14 ≤ 1261068471427 := by decide +kernel

theorem rows22240R_438 : rowsJ2 46 47 14 18 ≤ 2957805008972 := by decide +kernel

theorem rows22240R_439 : rowsJ2 46 47 18 21 ≤ 2360480426715 := by decide +kernel

theorem rows22240R_440 : rowsJ2 46 47 21 23 ≤ 1353713551728 := by decide +kernel

theorem rows22240R_441 : rowsJ2 46 47 23 25 ≤ 1120117439425 := by decide +kernel

theorem rows22240R_442 : rowsJ2 46 47 25 26 ≤ 476751184525 := by decide +kernel

theorem rows22240R_443 : rowsJ2 46 47 26 27 ≤ 428260981112 := by decide +kernel

theorem rows22240R_444 : rowsJ2 46 47 27 28 ≤ 382782205863 := by decide +kernel

theorem rows22240R_445 : rowsJ2 46 47 28 29 ≤ 349223516863 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_434
#print axioms SieveCert.rows22240R_445
