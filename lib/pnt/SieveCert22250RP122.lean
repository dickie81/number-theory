/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1362–1378 of 4715

File 122 of 351: the parts `rows22250R_1362` … `rows22250R_1378` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 95892 in units of a depth-4 test: row 70 columns 70–339, row 71 columns
0–17, row 71 columns 18–20, row 71 columns 21–21, row 71 columns 22–22, row 71 columns 23–23, row 71 columns 24–24,
row 71 columns 25–25, row 71 columns 26–26, row 71 columns 27–27, row 71 columns 28–28, row 71 columns 29–29, row 71
columns 30–31, row 71 columns 32–33, row 71 columns 34–35, row 71 columns 36–37, row 71 columns 38–39), each a sum
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

theorem rows22250R_1362 : rowsJ2 70 71 70 340 ≤ 1221331561869 := by decide +kernel

theorem rows22250R_1363 : rowsJ2 71 72 0 18 ≤ 738056993557 := by decide +kernel

theorem rows22250R_1364 : rowsJ2 71 72 18 21 ≤ 0 := by decide +kernel

theorem rows22250R_1365 : rowsJ2 71 72 21 22 ≤ 0 := by decide +kernel

theorem rows22250R_1366 : rowsJ2 71 72 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1367 : rowsJ2 71 72 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1368 : rowsJ2 71 72 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1369 : rowsJ2 71 72 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1370 : rowsJ2 71 72 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1371 : rowsJ2 71 72 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1372 : rowsJ2 71 72 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1373 : rowsJ2 71 72 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1374 : rowsJ2 71 72 30 32 ≤ 0 := by decide +kernel

theorem rows22250R_1375 : rowsJ2 71 72 32 34 ≤ 0 := by decide +kernel

theorem rows22250R_1376 : rowsJ2 71 72 34 36 ≤ 0 := by decide +kernel

theorem rows22250R_1377 : rowsJ2 71 72 36 38 ≤ 0 := by decide +kernel

theorem rows22250R_1378 : rowsJ2 71 72 38 40 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1362
#print axioms SieveCert.rows22250R_1378
