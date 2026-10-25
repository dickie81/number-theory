/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1676–1681 of 1732

File 420 of 430: the parts `rows22310R_1676` … `rows22310R_1681` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (6 parts, 28336 tests: rows 259–260, rows 261–261, rows 262–262, rows 263–263, rows
264–264, rows 265–265), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1676 : rows2 259 261 ≤ 12362465159667098 := by decide +kernel

theorem rows22310R_1677 : rows2 261 262 ≤ 6267210985857804 := by decide +kernel

theorem rows22310R_1678 : rows2 262 263 ≤ 6351536626325552 := by decide +kernel

theorem rows22310R_1679 : rows2 263 264 ≤ 6401124066388002 := by decide +kernel

theorem rows22310R_1680 : rows2 264 265 ≤ 6488564313167159 := by decide +kernel

theorem rows22310R_1681 : rows2 265 266 ≤ 6540474503681234 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1676
#print axioms SieveCert.rows22310R_1681
