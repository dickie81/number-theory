/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 514–517 of 1732

File 130 of 430: the parts `rows22310R_514` … `rows22310R_517` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28700 tests: row 106 columns 53–73, row 106 columns 74–82, row 106 columns
83–86, row 106 columns 87–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_514 : rowsJ2 106 107 53 74 ≤ 319482741921868 := by decide +kernel

theorem rows22310R_515 : rowsJ2 106 107 74 83 ≤ 40212901618491 := by decide +kernel

theorem rows22310R_516 : rowsJ2 106 107 83 87 ≤ 4941940834045 := by decide +kernel

theorem rows22310R_517 : rowsJ2 106 107 87 90 ≤ 1448650088222 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_514
#print axioms SieveCert.rows22310R_517
