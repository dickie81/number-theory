/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1456–1459 of 1732

File 366 of 430: the parts `rows22310R_1456` … `rows22310R_1459` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28056 tests: row 173 columns 77–399, row 174 columns 0–52, row 174 columns
53–57, row 174 columns 58–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1456 : rowsJ2 173 174 77 400 ≤ 1565809219327447 := by decide +kernel

theorem rows22310R_1457 : rowsJ2 174 175 0 53 ≤ 57324367800685 := by decide +kernel

theorem rows22310R_1458 : rowsJ2 174 175 53 58 ≤ 26963363393783 := by decide +kernel

theorem rows22310R_1459 : rowsJ2 174 175 58 62 ≤ 32965629293161 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1456
#print axioms SieveCert.rows22310R_1459
