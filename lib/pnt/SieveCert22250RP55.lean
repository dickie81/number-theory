/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 525–530 of 5796

File 55 of 465: the parts `rows22250R_525` … `rows22250R_530` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 99915 tests: row 49 columns 33–33, row 49 columns 34–34, row 49 columns
35–35, row 49 columns 36–36, row 49 columns 37–37, row 49 columns 38–38), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_525 : rowsJ2 49 50 33 34 ≤ 124053236788 := by decide +kernel

theorem rows22250R_526 : rowsJ2 49 50 34 35 ≤ 103341400440 := by decide +kernel

theorem rows22250R_527 : rowsJ2 49 50 35 36 ≤ 85891921841 := by decide +kernel

theorem rows22250R_528 : rowsJ2 49 50 36 37 ≤ 67087258372 := by decide +kernel

theorem rows22250R_529 : rowsJ2 49 50 37 38 ≤ 53495243037 := by decide +kernel

theorem rows22250R_530 : rowsJ2 49 50 38 39 ≤ 39998407079 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_525
#print axioms SieveCert.rows22250R_530
