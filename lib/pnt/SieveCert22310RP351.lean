/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1397–1400 of 1732

File 351 of 430: the parts `rows22310R_1397` … `rows22310R_1400` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28405 tests: row 166 columns 69–72, row 166 columns 73–76, row 166 columns
77–81, row 166 columns 82–87), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1397 : rowsJ2 166 167 69 73 ≤ 23061260655420 := by decide +kernel

theorem rows22310R_1398 : rowsJ2 166 167 73 77 ≤ 14210869008415 := by decide +kernel

theorem rows22310R_1399 : rowsJ2 166 167 77 82 ≤ 8704666761166 := by decide +kernel

theorem rows22310R_1400 : rowsJ2 166 167 82 88 ≤ 2558052046524 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1397
#print axioms SieveCert.rows22310R_1400
