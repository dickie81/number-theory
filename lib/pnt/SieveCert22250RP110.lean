/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1214–1222 of 4715

File 110 of 351: the parts `rows22250R_1214` … `rows22250R_1222` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, work 96190 in units of a depth-4 test: row 67 columns 57–57, row 67 columns
58–58, row 67 columns 59–59, row 67 columns 60–60, row 67 columns 61–61, row 67 columns 62–62, row 67 columns 63–63,
row 67 columns 64–64, row 67 columns 65–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1214 : rowsJ2 67 68 57 58 ≤ 7994461277584 := by decide +kernel

theorem rows22250R_1215 : rowsJ2 67 68 58 59 ≤ 7590794595497 := by decide +kernel

theorem rows22250R_1216 : rowsJ2 67 68 59 60 ≤ 7191889851672 := by decide +kernel

theorem rows22250R_1217 : rowsJ2 67 68 60 61 ≤ 6783721879545 := by decide +kernel

theorem rows22250R_1218 : rowsJ2 67 68 61 62 ≤ 6380004134896 := by decide +kernel

theorem rows22250R_1219 : rowsJ2 67 68 62 63 ≤ 5966340348017 := by decide +kernel

theorem rows22250R_1220 : rowsJ2 67 68 63 64 ≤ 5556815485323 := by decide +kernel

theorem rows22250R_1221 : rowsJ2 67 68 64 65 ≤ 5136638335061 := by decide +kernel

theorem rows22250R_1222 : rowsJ2 67 68 65 66 ≤ 4720286579292 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1214
#print axioms SieveCert.rows22250R_1222
