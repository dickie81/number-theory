/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1144–1146 of 1732

File 287 of 430: the parts `rows22310R_1144` … `rows22310R_1146` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 23189 tests: row 143 columns 97–101, row 143 columns 102–399, row 144 columns
0–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_1144 : rowsJ2 143 144 97 102 ≤ 532223654760 := by decide +kernel

theorem rows22310R_1145 : rowsJ2 143 144 102 400 ≤ 383876371314209 := by decide +kernel

theorem rows22310R_1146 : rowsJ2 144 145 0 60 ≤ 246010005818840 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1144
#print axioms SieveCert.rows22310R_1146
