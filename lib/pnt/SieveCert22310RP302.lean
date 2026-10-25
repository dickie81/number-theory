/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1203–1206 of 1732

File 302 of 430: the parts `rows22310R_1203` … `rows22310R_1206` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27807 tests: row 148 columns 76–78, row 148 columns 79–81, row 148 columns
82–84, row 148 columns 85–88), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1203 : rowsJ2 148 149 76 79 ≤ 10276636784343 := by decide +kernel

theorem rows22310R_1204 : rowsJ2 148 149 79 82 ≤ 6812295623990 := by decide +kernel

theorem rows22310R_1205 : rowsJ2 148 149 82 85 ≤ 4041174037355 := by decide +kernel

theorem rows22310R_1206 : rowsJ2 148 149 85 89 ≤ 2181404547735 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1203
#print axioms SieveCert.rows22310R_1206
