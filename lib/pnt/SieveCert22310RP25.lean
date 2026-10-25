/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 100–103 of 1732

File 25 of 430: the parts `rows22310R_100` … `rows22310R_103` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 61 columns 0–34, row 61 columns 35–43, row 61 columns 44–49,
row 61 columns 50–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_100 : rowsJ2 61 62 0 35 ≤ 1147355513204249 := by decide +kernel

theorem rows22310R_101 : rowsJ2 61 62 35 44 ≤ 400555166715482 := by decide +kernel

theorem rows22310R_102 : rowsJ2 61 62 44 50 ≤ 175545838297080 := by decide +kernel

theorem rows22310R_103 : rowsJ2 61 62 50 55 ≤ 129628936447476 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_100
#print axioms SieveCert.rows22310R_103
