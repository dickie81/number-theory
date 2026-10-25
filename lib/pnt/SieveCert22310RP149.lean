/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 590–593 of 1732

File 149 of 430: the parts `rows22310R_590` … `rows22310R_593` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25047 tests: row 110 columns 102–103, row 110 columns 104–105, row 110
columns 106–107, row 110 columns 108–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_590 : rowsJ2 110 111 102 104 ≤ 2233750195073 := by decide +kernel

theorem rows22310R_591 : rowsJ2 110 111 104 106 ≤ 2332416252985 := by decide +kernel

theorem rows22310R_592 : rowsJ2 110 111 106 108 ≤ 2704874880017 := by decide +kernel

theorem rows22310R_593 : rowsJ2 110 111 108 400 ≤ 5375043587448 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_590
#print axioms SieveCert.rows22310R_593
