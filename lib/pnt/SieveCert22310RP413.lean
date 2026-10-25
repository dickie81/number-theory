/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1643–1649 of 1732

File 413 of 430: the parts `rows22310R_1643` … `rows22310R_1649` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (7 parts, 28543 tests: row 218 columns 100–399, row 219 columns 0–106, row 219 columns
107–399, row 220 columns 0–114, row 220 columns 115–399, row 221 columns 0–124, row 221 columns 125–399), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1643 : rowsJ2 218 219 100 400 ≤ 2929401975067415 := by decide +kernel

theorem rows22310R_1644 : rowsJ2 219 220 0 107 ≤ 713449055914463 := by decide +kernel

theorem rows22310R_1645 : rowsJ2 219 220 107 400 ≤ 2491196850090436 := by decide +kernel

theorem rows22310R_1646 : rowsJ2 220 221 0 115 ≤ 1252196981465020 := by decide +kernel

theorem rows22310R_1647 : rowsJ2 220 221 115 400 ≤ 2035101996456660 := by decide +kernel

theorem rows22310R_1648 : rowsJ2 221 222 0 125 ≤ 1840947608448007 := by decide +kernel

theorem rows22310R_1649 : rowsJ2 221 222 125 400 ≤ 1529112635936594 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1643
#print axioms SieveCert.rows22310R_1649
