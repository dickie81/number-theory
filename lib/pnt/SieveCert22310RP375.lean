/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1492–1494 of 1732

File 375 of 430: the parts `rows22310R_1492` … `rows22310R_1494` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22067 tests: row 179 columns 0–50, row 179 columns 51–56, row 179 columns
57–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_1492 : rowsJ2 179 180 0 51 ≤ 43933953146075 := by decide +kernel

theorem rows22310R_1493 : rowsJ2 179 180 51 57 ≤ 38785242457271 := by decide +kernel

theorem rows22310R_1494 : rowsJ2 179 180 57 61 ≤ 39140428317319 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1492
#print axioms SieveCert.rows22310R_1494
