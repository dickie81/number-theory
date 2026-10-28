/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1262–1279 of 5066

File 122 of 387: the parts `rows22240R_1262` … `rows22240R_1279` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (18 parts, work 96163 in units of a depth-4 test: row 68 columns 27–27, row 68 columns
28–28, row 68 columns 29–29, row 68 columns 30–30, row 68 columns 31–31, row 68 columns 32–32, row 68 columns 33–33,
row 68 columns 34–34, row 68 columns 35–35, row 68 columns 36–36, row 68 columns 37–37, row 68 columns 38–38, row 68
columns 39–39, row 68 columns 40–40, row 68 columns 41–41, row 68 columns 42–42, row 68 columns 43–43, row 68
columns 44–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_1262 : rowsJ2 68 69 27 28 ≤ 0 := by decide +kernel

theorem rows22240R_1263 : rowsJ2 68 69 28 29 ≤ 0 := by decide +kernel

theorem rows22240R_1264 : rowsJ2 68 69 29 30 ≤ 0 := by decide +kernel

theorem rows22240R_1265 : rowsJ2 68 69 30 31 ≤ 0 := by decide +kernel

theorem rows22240R_1266 : rowsJ2 68 69 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_1267 : rowsJ2 68 69 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_1268 : rowsJ2 68 69 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_1269 : rowsJ2 68 69 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_1270 : rowsJ2 68 69 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_1271 : rowsJ2 68 69 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_1272 : rowsJ2 68 69 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_1273 : rowsJ2 68 69 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_1274 : rowsJ2 68 69 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_1275 : rowsJ2 68 69 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_1276 : rowsJ2 68 69 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1277 : rowsJ2 68 69 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1278 : rowsJ2 68 69 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1279 : rowsJ2 68 69 44 45 ≤ 65080792073 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1262
#print axioms SieveCert.rows22240R_1279
