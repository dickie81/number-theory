/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 14–19 of 1732

File 4 of 430: the parts `rows22310R_14` … `rows22310R_19` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (6 parts, 29679 tests: row 36 columns 0–34, row 36 columns 35–399, row 37 columns 0–34,
row 37 columns 35–399, row 38 columns 0–34, row 38 columns 35–399), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_14 : rowsJ2 36 37 0 35 ≤ 1547449618206447 := by decide +kernel

theorem rows22310R_15 : rowsJ2 36 37 35 400 ≤ 200422601175529 := by decide +kernel

theorem rows22310R_16 : rowsJ2 37 38 0 35 ≤ 1531314984661707 := by decide +kernel

theorem rows22310R_17 : rowsJ2 37 38 35 400 ≤ 298287940533443 := by decide +kernel

theorem rows22310R_18 : rowsJ2 38 39 0 35 ≤ 1515335423550640 := by decide +kernel

theorem rows22310R_19 : rowsJ2 38 39 35 400 ≤ 393418265354272 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_14
#print axioms SieveCert.rows22310R_19
