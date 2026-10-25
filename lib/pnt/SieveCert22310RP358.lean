/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1424–1427 of 1732

File 358 of 430: the parts `rows22310R_1424` … `rows22310R_1427` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27656 tests: row 169 columns 77–82, row 169 columns 83–399, row 170 columns
0–53, row 170 columns 54–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1424 : rowsJ2 169 170 77 83 ≤ 7273114938270 := by decide +kernel

theorem rows22310R_1425 : rowsJ2 169 170 83 400 ≤ 1211774004082497 := by decide +kernel

theorem rows22310R_1426 : rowsJ2 170 171 0 54 ≤ 69619041058614 := by decide +kernel

theorem rows22310R_1427 : rowsJ2 170 171 54 60 ≤ 28982631570190 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1424
#print axioms SieveCert.rows22310R_1427
