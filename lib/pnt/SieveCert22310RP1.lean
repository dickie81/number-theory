/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 0–3 of 1732

File 1 of 430: the parts `rows22310R_0` … `rows22310R_3` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27405 tests: rows 0–18, rows 19–22, rows 23–24, rows 25–26), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_0 : rows2 0 19 ≤ 2867932252020023 := by decide +kernel

theorem rows22310R_1 : rows2 19 23 ≤ 2375384428091380 := by decide +kernel

theorem rows22310R_2 : rows2 23 25 ≤ 1560226842472049 := by decide +kernel

theorem rows22310R_3 : rows2 25 27 ≤ 1833272051440733 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_0
#print axioms SieveCert.rows22310R_3
