/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1221–1227 of 5796

File 126 of 465: the parts `rows22250R_1221` … `rows22250R_1227` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 95149 tests: row 67 columns 54–54, row 67 columns 55–55, row 67 columns
56–56, row 67 columns 57–57, row 67 columns 58–58, row 67 columns 59–59, row 67 columns 60–60), each a sum of
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

theorem rows22250R_1221 : rowsJ2 67 68 54 55 ≤ 4455352245806 := by decide +kernel

theorem rows22250R_1222 : rowsJ2 67 68 55 56 ≤ 5424663540025 := by decide +kernel

theorem rows22250R_1223 : rowsJ2 67 68 56 57 ≤ 6434449807985 := by decide +kernel

theorem rows22250R_1224 : rowsJ2 67 68 57 58 ≤ 7356247187498 := by decide +kernel

theorem rows22250R_1225 : rowsJ2 67 68 58 59 ≤ 8094949268519 := by decide +kernel

theorem rows22250R_1226 : rowsJ2 67 68 59 60 ≤ 8800102263698 := by decide +kernel

theorem rows22250R_1227 : rowsJ2 67 68 60 61 ≤ 9542310544474 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1221
#print axioms SieveCert.rows22250R_1227
