/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 618–621 of 1732

File 156 of 430: the parts `rows22310R_618` … `rows22310R_621` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26460 tests: row 112 columns 87–89, row 112 columns 90–91, row 112 columns
92–93, row 112 columns 94–95), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_618 : rowsJ2 112 113 87 90 ≤ 998923417014 := by decide +kernel

theorem rows22310R_619 : rowsJ2 112 113 90 92 ≤ 1592092117884 := by decide +kernel

theorem rows22310R_620 : rowsJ2 112 113 92 94 ≤ 2638704262012 := by decide +kernel

theorem rows22310R_621 : rowsJ2 112 113 94 96 ≤ 2655170468503 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_618
#print axioms SieveCert.rows22310R_621
