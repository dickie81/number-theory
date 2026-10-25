/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1577–1580 of 1732

File 397 of 430: the parts `rows22310R_1577` … `rows22310R_1580` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26949 tests: row 195 columns 45–50, row 195 columns 51–56, row 195 columns
57–399, row 196 columns 0–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1577 : rowsJ2 195 196 45 51 ≤ 60502838452357 := by decide +kernel

theorem rows22310R_1578 : rowsJ2 195 196 51 57 ≤ 68307146505535 := by decide +kernel

theorem rows22310R_1579 : rowsJ2 195 196 57 400 ≤ 2123985382433159 := by decide +kernel

theorem rows22310R_1580 : rowsJ2 196 197 0 44 ≤ 29466101384536 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1577
#print axioms SieveCert.rows22310R_1580
