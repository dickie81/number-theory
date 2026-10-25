/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1307–1310 of 1732

File 328 of 430: the parts `rows22310R_1307` … `rows22310R_1310` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26073 tests: row 157 columns 64–67, row 157 columns 68–70, row 157 columns
71–73, row 157 columns 74–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1307 : rowsJ2 157 158 64 68 ≤ 20699431442998 := by decide +kernel

theorem rows22310R_1308 : rowsJ2 157 158 68 71 ≤ 19704324075147 := by decide +kernel

theorem rows22310R_1309 : rowsJ2 157 158 71 74 ≤ 18523270119530 := by decide +kernel

theorem rows22310R_1310 : rowsJ2 157 158 74 77 ≤ 13772005182802 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1307
#print axioms SieveCert.rows22310R_1310
