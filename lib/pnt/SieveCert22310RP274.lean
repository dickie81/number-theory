/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1093–1096 of 1732

File 274 of 430: the parts `rows22310R_1093` … `rows22310R_1096` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26450 tests: row 140 columns 58–67, row 140 columns 68–71, row 140 columns
72–74, row 140 columns 75–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1093 : rowsJ2 140 141 58 68 ≤ 7681996074189 := by decide +kernel

theorem rows22310R_1094 : rowsJ2 140 141 68 72 ≤ 7412768603648 := by decide +kernel

theorem rows22310R_1095 : rowsJ2 140 141 72 75 ≤ 5711004479740 := by decide +kernel

theorem rows22310R_1096 : rowsJ2 140 141 75 78 ≤ 4806574967348 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1093
#print axioms SieveCert.rows22310R_1096
