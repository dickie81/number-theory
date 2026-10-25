/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1273–1278 of 5796

File 131 of 465: the parts `rows22250R_1273` … `rows22250R_1278` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 92047 tests: row 68 columns 58–58, row 68 columns 59–59, row 68 columns
60–60, row 68 columns 61–61, row 68 columns 62–62, row 68 columns 63–63), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1273 : rowsJ2 68 69 58 59 ≤ 7781935940151 := by decide +kernel

theorem rows22250R_1274 : rowsJ2 68 69 59 60 ≤ 8395901531243 := by decide +kernel

theorem rows22250R_1275 : rowsJ2 68 69 60 61 ≤ 9084188306705 := by decide +kernel

theorem rows22250R_1276 : rowsJ2 68 69 61 62 ≤ 9582805466220 := by decide +kernel

theorem rows22250R_1277 : rowsJ2 68 69 62 63 ≤ 9167637435712 := by decide +kernel

theorem rows22250R_1278 : rowsJ2 68 69 63 64 ≤ 8702667347256 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1273
#print axioms SieveCert.rows22250R_1278
