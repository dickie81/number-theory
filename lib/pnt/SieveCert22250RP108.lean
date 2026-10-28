/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1189–1205 of 4715

File 108 of 351: the parts `rows22250R_1189` … `rows22250R_1205` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 95846 in units of a depth-4 test: row 67 columns 29–29, row 67 columns
30–30, row 67 columns 31–31, row 67 columns 32–32, row 67 columns 33–33, row 67 columns 34–34, row 67 columns 35–36,
row 67 columns 37–38, row 67 columns 39–40, row 67 columns 41–41, row 67 columns 42–42, row 67 columns 43–43, row 67
columns 44–44, row 67 columns 45–45, row 67 columns 46–46, row 67 columns 47–47, row 67 columns 48–48), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1189 : rowsJ2 67 68 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1190 : rowsJ2 67 68 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1191 : rowsJ2 67 68 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1192 : rowsJ2 67 68 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1193 : rowsJ2 67 68 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1194 : rowsJ2 67 68 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1195 : rowsJ2 67 68 35 37 ≤ 0 := by decide +kernel

theorem rows22250R_1196 : rowsJ2 67 68 37 39 ≤ 0 := by decide +kernel

theorem rows22250R_1197 : rowsJ2 67 68 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1198 : rowsJ2 67 68 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1199 : rowsJ2 67 68 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1200 : rowsJ2 67 68 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1201 : rowsJ2 67 68 44 45 ≤ 64705417320 := by decide +kernel

theorem rows22250R_1202 : rowsJ2 67 68 45 46 ≤ 253968914853 := by decide +kernel

theorem rows22250R_1203 : rowsJ2 67 68 46 47 ≤ 757677826083 := by decide +kernel

theorem rows22250R_1204 : rowsJ2 67 68 47 48 ≤ 1504630634466 := by decide +kernel

theorem rows22250R_1205 : rowsJ2 67 68 48 49 ≤ 2223317031637 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1189
#print axioms SieveCert.rows22250R_1205
