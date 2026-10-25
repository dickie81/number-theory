/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1184–1192 of 5796

File 123 of 465: the parts `rows22250R_1184` … `rows22250R_1192` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 96342 tests: row 66 columns 63–63, row 66 columns 64–64, row 66 columns
65–65, row 66 columns 66–359, row 67 columns 0–17, row 67 columns 18–21, row 67 columns 22–23, row 67 columns 24–24,
row 67 columns 25–25), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1184 : rowsJ2 66 67 63 64 ≤ 10630720966936 := by decide +kernel

theorem rows22250R_1185 : rowsJ2 66 67 64 65 ≤ 10163640732331 := by decide +kernel

theorem rows22250R_1186 : rowsJ2 66 67 65 66 ≤ 9645313090651 := by decide +kernel

theorem rows22250R_1187 : rowsJ2 66 67 66 360 ≤ 9172916146357 := by decide +kernel

theorem rows22250R_1188 : rowsJ2 67 68 0 18 ≤ 1552181068666 := by decide +kernel

theorem rows22250R_1189 : rowsJ2 67 68 18 22 ≤ 102942556919 := by decide +kernel

theorem rows22250R_1190 : rowsJ2 67 68 22 24 ≤ 9915154368 := by decide +kernel

theorem rows22250R_1191 : rowsJ2 67 68 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1192 : rowsJ2 67 68 25 26 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1184
#print axioms SieveCert.rows22250R_1192
