/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 942–945 of 1732

File 236 of 430: the parts `rows22310R_942` … `rows22310R_945` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28710 tests: row 130 columns 35–67, row 130 columns 68–73, row 130 columns
74–77, row 130 columns 78–80), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_942 : rowsJ2 130 131 35 68 ≤ 255566764518194 := by decide +kernel

theorem rows22310R_943 : rowsJ2 130 131 68 74 ≤ 1025736544821 := by decide +kernel

theorem rows22310R_944 : rowsJ2 130 131 74 78 ≤ 0 := by decide +kernel

theorem rows22310R_945 : rowsJ2 130 131 78 81 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_942
#print axioms SieveCert.rows22310R_945
