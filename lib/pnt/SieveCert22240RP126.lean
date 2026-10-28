/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1308–1324 of 5066

File 126 of 387: the parts `rows22240R_1308` … `rows22240R_1324` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 96210 in units of a depth-4 test: row 69 columns 24–24, row 69 columns
25–25, row 69 columns 26–26, row 69 columns 27–27, row 69 columns 28–28, row 69 columns 29–29, row 69 columns 30–30,
row 69 columns 31–31, row 69 columns 32–32, row 69 columns 33–33, row 69 columns 34–34, row 69 columns 35–35, row 69
columns 36–36, row 69 columns 37–37, row 69 columns 38–39, row 69 columns 40–40, row 69 columns 41–41), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1308 : rowsJ2 69 70 24 25 ≤ 0 := by decide +kernel

theorem rows22240R_1309 : rowsJ2 69 70 25 26 ≤ 0 := by decide +kernel

theorem rows22240R_1310 : rowsJ2 69 70 26 27 ≤ 0 := by decide +kernel

theorem rows22240R_1311 : rowsJ2 69 70 27 28 ≤ 0 := by decide +kernel

theorem rows22240R_1312 : rowsJ2 69 70 28 29 ≤ 0 := by decide +kernel

theorem rows22240R_1313 : rowsJ2 69 70 29 30 ≤ 0 := by decide +kernel

theorem rows22240R_1314 : rowsJ2 69 70 30 31 ≤ 0 := by decide +kernel

theorem rows22240R_1315 : rowsJ2 69 70 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_1316 : rowsJ2 69 70 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_1317 : rowsJ2 69 70 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_1318 : rowsJ2 69 70 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_1319 : rowsJ2 69 70 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_1320 : rowsJ2 69 70 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_1321 : rowsJ2 69 70 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_1322 : rowsJ2 69 70 38 40 ≤ 0 := by decide +kernel

theorem rows22240R_1323 : rowsJ2 69 70 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_1324 : rowsJ2 69 70 41 42 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1308
#print axioms SieveCert.rows22240R_1324
