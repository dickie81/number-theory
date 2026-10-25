/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1668–1671 of 1732

File 418 of 430: the parts `rows22310R_1668` … `rows22310R_1671` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28436 tests: rows 243–244, rows 245–246, rows 247–248, rows 249–250), each a
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

theorem rows22310R_1668 : rows2 243 245 ≤ 10550756328090835 := by decide +kernel

theorem rows22310R_1669 : rows2 245 247 ≤ 10922103630914472 := by decide +kernel

theorem rows22310R_1670 : rows2 247 249 ≤ 11120715813651480 := by decide +kernel

theorem rows22310R_1671 : rows2 249 251 ≤ 11294767700761918 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1668
#print axioms SieveCert.rows22310R_1671
