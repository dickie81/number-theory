/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1121–1124 of 1732

File 281 of 430: the parts `rows22310R_1121` … `rows22310R_1124` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27911 tests: row 142 columns 59–66, row 142 columns 67–71, row 142 columns
72–74, row 142 columns 75–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1121 : rowsJ2 142 143 59 67 ≤ 7779579849800 := by decide +kernel

theorem rows22310R_1122 : rowsJ2 142 143 67 72 ≤ 11039720455912 := by decide +kernel

theorem rows22310R_1123 : rowsJ2 142 143 72 75 ≤ 7276618030152 := by decide +kernel

theorem rows22310R_1124 : rowsJ2 142 143 75 78 ≤ 6643576051701 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1121
#print axioms SieveCert.rows22310R_1124
