/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 9–13 of 1732

File 3 of 430: the parts `rows22310R_9` … `rows22310R_13` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 29891 tests: rows 32–32, rows 33–33, rows 34–34, row 35 columns 0–34, row 35
columns 35–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_9 : rows2 32 33 ≤ 1413830525972619 := by decide +kernel

theorem rows22310R_10 : rows2 33 34 ≤ 1496593957479245 := by decide +kernel

theorem rows22310R_11 : rows2 34 35 ≤ 1580467800325530 := by decide +kernel

theorem rows22310R_12 : rowsJ2 35 36 0 35 ≤ 1563830372240459 := by decide +kernel

theorem rows22310R_13 : rowsJ2 35 36 35 400 ≤ 100682963062383 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_9
#print axioms SieveCert.rows22310R_13
