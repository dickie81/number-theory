/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 459–468 of 5066

File 45 of 387: the parts `rows22240R_459` … `rows22240R_468` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 99046 in units of a depth-4 test: row 46 columns 42–42, row 46 columns
43–43, row 46 columns 44–44, row 46 columns 45–45, row 46 columns 46–339, row 47 columns 0–13, row 47 columns 14–17,
row 47 columns 18–20, row 47 columns 21–23, row 47 columns 24–25), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_459 : rowsJ2 46 47 42 43 ≤ 33992412153 := by decide +kernel

theorem rows22240R_460 : rowsJ2 46 47 43 44 ≤ 21005005155 := by decide +kernel

theorem rows22240R_461 : rowsJ2 46 47 44 45 ≤ 15784172247 := by decide +kernel

theorem rows22240R_462 : rowsJ2 46 47 45 46 ≤ 244728520506 := by decide +kernel

theorem rows22240R_463 : rowsJ2 46 47 46 340 ≤ 467242523130 := by decide +kernel

theorem rows22240R_464 : rowsJ2 47 48 0 14 ≤ 1372431850544 := by decide +kernel

theorem rows22240R_465 : rowsJ2 47 48 14 18 ≤ 2887613782060 := by decide +kernel

theorem rows22240R_466 : rowsJ2 47 48 18 21 ≤ 2198865368396 := by decide +kernel

theorem rows22240R_467 : rowsJ2 47 48 21 24 ≤ 1773689395081 := by decide +kernel

theorem rows22240R_468 : rowsJ2 47 48 24 26 ≤ 907331630460 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_459
#print axioms SieveCert.rows22240R_468
