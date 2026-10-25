/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1065–1068 of 1732

File 267 of 430: the parts `rows22310R_1065` … `rows22310R_1068` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27587 tests: row 138 columns 43–67, row 138 columns 68–72, row 138 columns
73–75, row 138 columns 76–78), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1065 : rowsJ2 138 139 43 68 ≤ 47778011117035 := by decide +kernel

theorem rows22310R_1066 : rowsJ2 138 139 68 73 ≤ 7363982810937 := by decide +kernel

theorem rows22310R_1067 : rowsJ2 138 139 73 76 ≤ 3969498633336 := by decide +kernel

theorem rows22310R_1068 : rowsJ2 138 139 76 79 ≤ 2477350247786 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1065
#print axioms SieveCert.rows22310R_1068
