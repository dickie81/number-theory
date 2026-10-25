/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 64–67 of 1732

File 16 of 430: the parts `rows22310R_64` … `rows22310R_67` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 54 columns 0–34, row 54 columns 35–43, row 54 columns 44–49,
row 54 columns 50–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22310R_64 : rowsJ2 54 55 0 35 ≤ 1267784722551029 := by decide +kernel

theorem rows22310R_65 : rowsJ2 54 55 35 44 ≤ 556865729700971 := by decide +kernel

theorem rows22310R_66 : rowsJ2 54 55 44 50 ≤ 259459430568531 := by decide +kernel

theorem rows22310R_67 : rowsJ2 54 55 50 400 ≤ 174810084625316 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_64
#print axioms SieveCert.rows22310R_67
