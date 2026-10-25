/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1650–1653 of 1732

File 414 of 430: the parts `rows22310R_1650` … `rows22310R_1653` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29325 tests: rows 222–222, rows 223–223, rows 224–224, rows 225–225), each a
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

theorem rows22310R_1650 : rows2 222 223 ≤ 3452925212107421 := by decide +kernel

theorem rows22310R_1651 : rows2 223 224 ≤ 3535888916508753 := by decide +kernel

theorem rows22310R_1652 : rows2 224 225 ≤ 3618905536891858 := by decide +kernel

theorem rows22310R_1653 : rows2 225 226 ≤ 3701967881942032 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1650
#print axioms SieveCert.rows22310R_1653
