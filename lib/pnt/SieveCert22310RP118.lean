/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 469–471 of 1732

File 118 of 430: the parts `rows22310R_469` … `rows22310R_471` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 23168 tests: row 103 columns 35–43, row 103 columns 44–51, row 103 columns
52–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_469 : rowsJ2 103 104 35 44 ≤ 121437570803450 := by decide +kernel

theorem rows22310R_470 : rowsJ2 103 104 44 52 ≤ 243292135646114 := by decide +kernel

theorem rows22310R_471 : rowsJ2 103 104 52 65 ≤ 282755651134344 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_469
#print axioms SieveCert.rows22310R_471
