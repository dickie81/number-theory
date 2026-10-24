/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 136–139 of 549

File 36 of 140: the parts `rows22335R_136` … `rows22335R_139` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24137 tests: row 73 columns 58–67, row 73 columns 68–72, row 73 columns
73–299, row 74 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_136 : rowsJ2 73 74 58 68 ≤ 93806915989068 := by decide +kernel

theorem rows22335R_137 : rowsJ2 73 74 68 73 ≤ 22066239862757 := by decide +kernel

theorem rows22335R_138 : rowsJ2 73 74 73 300 ≤ 6930927254461 := by decide +kernel

theorem rows22335R_139 : rowsJ2 74 75 0 35 ≤ 532172911556401 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_136
#print axioms SieveCert.rows22335R_139
