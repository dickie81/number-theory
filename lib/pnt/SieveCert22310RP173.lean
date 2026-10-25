/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 687–689 of 1732

File 173 of 430: the parts `rows22310R_687` … `rows22310R_689` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 23544 tests: row 116 columns 35–45, row 116 columns 46–72, row 116 columns
73–79), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_687 : rowsJ2 116 117 35 46 ≤ 258288500426694 := by decide +kernel

theorem rows22310R_688 : rowsJ2 116 117 46 73 ≤ 298739425228203 := by decide +kernel

theorem rows22310R_689 : rowsJ2 116 117 73 80 ≤ 5296647342747 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_687
#print axioms SieveCert.rows22310R_689
