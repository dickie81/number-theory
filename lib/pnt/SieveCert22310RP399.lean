/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1585–1588 of 1732

File 399 of 430: the parts `rows22310R_1585` … `rows22310R_1588` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26070 tests: row 197 columns 44–50, row 197 columns 51–56, row 197 columns
57–399, row 198 columns 0–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1585 : rowsJ2 197 198 44 51 ≤ 76418698171940 := by decide +kernel

theorem rows22310R_1586 : rowsJ2 197 198 51 57 ≤ 65002020624104 := by decide +kernel

theorem rows22310R_1587 : rowsJ2 197 198 57 400 ≤ 2130569212047710 := by decide +kernel

theorem rows22310R_1588 : rowsJ2 198 199 0 44 ≤ 35848696206427 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1585
#print axioms SieveCert.rows22310R_1588
