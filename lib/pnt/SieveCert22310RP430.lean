/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1728–1731 of 1732

File 430 of 430: the parts `rows22310R_1728` … `rows22310R_1731` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24284 tests: rows 392–393, rows 394–395, rows 396–397, rows 398–399), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1728 : rows2 392 394 ≤ 20105693141087827 := by decide +kernel

theorem rows22310R_1729 : rows2 394 396 ≤ 20671349338888422 := by decide +kernel

theorem rows22310R_1730 : rows2 396 398 ≤ 21258637002328640 := by decide +kernel

theorem rows22310R_1731 : rows2 398 400 ≤ 21881208152228591 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1728
#print axioms SieveCert.rows22310R_1731
