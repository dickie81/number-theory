/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1178–1183 of 5796

File 122 of 465: the parts `rows22250R_1178` … `rows22250R_1183` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 91971 tests: row 66 columns 57–57, row 66 columns 58–58, row 66 columns
59–59, row 66 columns 60–60, row 66 columns 61–61, row 66 columns 62–62), each a sum of refined costs (`rows2` or
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

theorem rows22250R_1178 : rowsJ2 66 67 57 58 ≤ 7580406508637 := by decide +kernel

theorem rows22250R_1179 : rowsJ2 66 67 58 59 ≤ 8408435045893 := by decide +kernel

theorem rows22250R_1180 : rowsJ2 66 67 59 60 ≤ 9164975134075 := by decide +kernel

theorem rows22250R_1181 : rowsJ2 66 67 60 61 ≤ 10000528632186 := by decide +kernel

theorem rows22250R_1182 : rowsJ2 66 67 61 62 ≤ 10648028515783 := by decide +kernel

theorem rows22250R_1183 : rowsJ2 66 67 62 63 ≤ 11143564090535 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1178
#print axioms SieveCert.rows22250R_1183
