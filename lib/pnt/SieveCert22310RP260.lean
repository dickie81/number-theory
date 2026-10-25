/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1038–1041 of 1732

File 260 of 430: the parts `rows22310R_1038` … `rows22310R_1041` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27951 tests: row 136 columns 77–79, row 136 columns 80–81, row 136 columns
82–84, row 136 columns 85–87), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1038 : rowsJ2 136 137 77 80 ≤ 267869246057 := by decide +kernel

theorem rows22310R_1039 : rowsJ2 136 137 80 82 ≤ 0 := by decide +kernel

theorem rows22310R_1040 : rowsJ2 136 137 82 85 ≤ 0 := by decide +kernel

theorem rows22310R_1041 : rowsJ2 136 137 85 88 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1038
#print axioms SieveCert.rows22310R_1041
