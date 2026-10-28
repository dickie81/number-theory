/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1215–1232 of 5066

File 118 of 387: the parts `rows22240R_1215` … `rows22240R_1232` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (18 parts, work 99638 in units of a depth-4 test: row 67 columns 28–28, row 67 columns
29–29, row 67 columns 30–30, row 67 columns 31–31, row 67 columns 32–32, row 67 columns 33–33, row 67 columns 34–34,
row 67 columns 35–35, row 67 columns 36–36, row 67 columns 37–37, row 67 columns 38–38, row 67 columns 39–39, row 67
columns 40–40, row 67 columns 41–41, row 67 columns 42–42, row 67 columns 43–43, row 67 columns 44–44, row 67
columns 45–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1215 : rowsJ2 67 68 28 29 ≤ 0 := by decide +kernel

theorem rows22240R_1216 : rowsJ2 67 68 29 30 ≤ 0 := by decide +kernel

theorem rows22240R_1217 : rowsJ2 67 68 30 31 ≤ 0 := by decide +kernel

theorem rows22240R_1218 : rowsJ2 67 68 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_1219 : rowsJ2 67 68 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_1220 : rowsJ2 67 68 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_1221 : rowsJ2 67 68 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_1222 : rowsJ2 67 68 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_1223 : rowsJ2 67 68 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_1224 : rowsJ2 67 68 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_1225 : rowsJ2 67 68 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_1226 : rowsJ2 67 68 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_1227 : rowsJ2 67 68 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_1228 : rowsJ2 67 68 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1229 : rowsJ2 67 68 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1230 : rowsJ2 67 68 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1231 : rowsJ2 67 68 44 45 ≤ 65653485443 := by decide +kernel

theorem rows22240R_1232 : rowsJ2 67 68 45 46 ≤ 191999817798 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1215
#print axioms SieveCert.rows22240R_1232
