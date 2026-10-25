/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1694–1699 of 1732

File 423 of 430: the parts `rows22310R_1694` … `rows22310R_1699` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (6 parts, 26625 tests: rows 278–278, rows 279–279, rows 280–280, rows 281–281, rows
282–282, rows 283–283), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22310R_1694 : rows2 278 279 ≤ 7311475103176778 := by decide +kernel

theorem rows22310R_1695 : rows2 279 280 ≤ 7378932466890857 := by decide +kernel

theorem rows22310R_1696 : rows2 280 281 ≤ 7340959821156205 := by decide +kernel

theorem rows22310R_1697 : rows2 281 282 ≤ 7409178078042869 := by decide +kernel

theorem rows22310R_1698 : rows2 282 283 ≤ 7369900311559299 := by decide +kernel

theorem rows22310R_1699 : rows2 283 284 ≤ 7438881839673923 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1694
#print axioms SieveCert.rows22310R_1699
