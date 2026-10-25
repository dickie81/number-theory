/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1327–1330 of 1732

File 333 of 430: the parts `rows22310R_1327` … `rows22310R_1330` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27009 tests: row 159 columns 57–62, row 159 columns 63–66, row 159 columns
67–69, row 159 columns 70–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1327 : rowsJ2 159 160 57 63 ≤ 18413211284966 := by decide +kernel

theorem rows22310R_1328 : rowsJ2 159 160 63 67 ≤ 21418073142826 := by decide +kernel

theorem rows22310R_1329 : rowsJ2 159 160 67 70 ≤ 20858943350960 := by decide +kernel

theorem rows22310R_1330 : rowsJ2 159 160 70 73 ≤ 19821053242598 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1327
#print axioms SieveCert.rows22310R_1330
