/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1638–1642 of 1732

File 412 of 430: the parts `rows22310R_1638` … `rows22310R_1642` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 29412 tests: row 216 columns 0–37, row 216 columns 38–399, row 217 columns
0–37, row 217 columns 38–399, row 218 columns 0–99), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1638 : rowsJ2 216 217 0 38 ≤ 44417238732553 := by decide +kernel

theorem rows22310R_1639 : rowsJ2 216 217 38 400 ≤ 2913182357419887 := by decide +kernel

theorem rows22310R_1640 : rowsJ2 217 218 0 38 ≤ 48851245236625 := by decide +kernel

theorem rows22310R_1641 : rowsJ2 217 218 38 400 ≤ 2990942160914769 := by decide +kernel

theorem rows22310R_1642 : rowsJ2 218 219 0 100 ≤ 192741103837054 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1638
#print axioms SieveCert.rows22310R_1642
