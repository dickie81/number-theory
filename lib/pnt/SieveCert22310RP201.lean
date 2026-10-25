/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 802–805 of 1732

File 201 of 430: the parts `rows22310R_802` … `rows22310R_805` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27893 tests: row 122 columns 35–50, row 122 columns 51–73, row 122 columns
74–78, row 122 columns 79–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_802 : rowsJ2 122 123 35 51 ≤ 314221446152988 := by decide +kernel

theorem rows22310R_803 : rowsJ2 122 123 51 74 ≤ 117120610961444 := by decide +kernel

theorem rows22310R_804 : rowsJ2 122 123 74 79 ≤ 0 := by decide +kernel

theorem rows22310R_805 : rowsJ2 122 123 79 82 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_802
#print axioms SieveCert.rows22310R_805
