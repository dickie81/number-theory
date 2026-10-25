/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1484–1487 of 1732

File 373 of 430: the parts `rows22310R_1484` … `rows22310R_1487` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24095 tests: row 177 columns 77–399, row 178 columns 0–50, row 178 columns
51–56, row 178 columns 57–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1484 : rowsJ2 177 178 77 400 ≤ 1894065947616476 := by decide +kernel

theorem rows22310R_1485 : rowsJ2 178 179 0 51 ≤ 44611872767597 := by decide +kernel

theorem rows22310R_1486 : rowsJ2 178 179 51 57 ≤ 36267742426309 := by decide +kernel

theorem rows22310R_1487 : rowsJ2 178 179 57 61 ≤ 37899558384170 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1484
#print axioms SieveCert.rows22310R_1487
