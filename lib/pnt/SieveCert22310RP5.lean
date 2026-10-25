/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 20–23 of 1732

File 5 of 430: the parts `rows22310R_20` … `rows22310R_23` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23821 tests: row 39 columns 0–34, row 39 columns 35–399, row 40 columns 0–34,
row 40 columns 35–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22310R_20 : rowsJ2 39 40 0 35 ≤ 1499580805444593 := by decide +kernel

theorem rows22310R_21 : rowsJ2 39 40 35 400 ≤ 484855219376212 := by decide +kernel

theorem rows22310R_22 : rowsJ2 40 41 0 35 ≤ 1483959580275080 := by decide +kernel

theorem rows22310R_23 : rowsJ2 40 41 35 400 ≤ 571698340427867 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_20
#print axioms SieveCert.rows22310R_23
