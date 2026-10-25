/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1022–1025 of 1732

File 256 of 430: the parts `rows22310R_1022` … `rows22310R_1025` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25408 tests: row 135 columns 73–76, row 135 columns 77–79, row 135 columns
80–81, row 135 columns 82–83), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1022 : rowsJ2 135 136 73 77 ≤ 2111870280984 := by decide +kernel

theorem rows22310R_1023 : rowsJ2 135 136 77 80 ≤ 0 := by decide +kernel

theorem rows22310R_1024 : rowsJ2 135 136 80 82 ≤ 0 := by decide +kernel

theorem rows22310R_1025 : rowsJ2 135 136 82 84 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1022
#print axioms SieveCert.rows22310R_1025
