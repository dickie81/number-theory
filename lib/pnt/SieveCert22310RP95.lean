/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 379–382 of 1732

File 95 of 430: the parts `rows22310R_379` … `rows22310R_382` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29885 tests: row 95 columns 35–43, row 95 columns 44–49, row 95 columns
50–56, row 95 columns 57–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_379 : rowsJ2 95 96 35 44 ≤ 67704615391990 := by decide +kernel

theorem rows22310R_380 : rowsJ2 95 96 44 50 ≤ 156074484914476 := by decide +kernel

theorem rows22310R_381 : rowsJ2 95 96 50 57 ≤ 232441084020710 := by decide +kernel

theorem rows22310R_382 : rowsJ2 95 96 57 67 ≤ 253640868793810 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_379
#print axioms SieveCert.rows22310R_382
