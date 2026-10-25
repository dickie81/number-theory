/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 285–288 of 1732

File 71 of 430: the parts `rows22310R_285` … `rows22310R_288` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28416 tests: row 83 columns 66–73, row 83 columns 74–399, row 84 columns
0–34, row 84 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_285 : rowsJ2 83 84 66 74 ≤ 228361095533220 := by decide +kernel

theorem rows22310R_286 : rowsJ2 83 84 74 400 ≤ 207521379654785 := by decide +kernel

theorem rows22310R_287 : rowsJ2 84 85 0 35 ≤ 610800960281560 := by decide +kernel

theorem rows22310R_288 : rowsJ2 84 85 35 44 ≤ 74311377678766 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_285
#print axioms SieveCert.rows22310R_288
