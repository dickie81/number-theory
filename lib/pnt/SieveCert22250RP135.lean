/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1318–1324 of 5796

File 135 of 465: the parts `rows22250R_1318` … `rows22250R_1324` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 95841 tests: row 69 columns 54–54, row 69 columns 55–55, row 69 columns
56–56, row 69 columns 57–57, row 69 columns 58–58, row 69 columns 59–59, row 69 columns 60–60), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1318 : rowsJ2 69 70 54 55 ≤ 4341441865133 := by decide +kernel

theorem rows22250R_1319 : rowsJ2 69 70 55 56 ≤ 5176930107802 := by decide +kernel

theorem rows22250R_1320 : rowsJ2 69 70 56 57 ≤ 6048625132824 := by decide +kernel

theorem rows22250R_1321 : rowsJ2 69 70 57 58 ≤ 6831120186498 := by decide +kernel

theorem rows22250R_1322 : rowsJ2 69 70 58 59 ≤ 7429523834931 := by decide +kernel

theorem rows22250R_1323 : rowsJ2 69 70 59 60 ≤ 7991747452557 := by decide +kernel

theorem rows22250R_1324 : rowsJ2 69 70 60 61 ≤ 8585758899971 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1318
#print axioms SieveCert.rows22250R_1324
