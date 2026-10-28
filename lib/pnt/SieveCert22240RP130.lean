/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1357–1372 of 5066

File 130 of 387: the parts `rows22240R_1357` … `rows22240R_1372` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96672 in units of a depth-4 test: row 70 columns 23–23, row 70 columns
24–24, row 70 columns 25–25, row 70 columns 26–26, row 70 columns 27–27, row 70 columns 28–28, row 70 columns 29–29,
row 70 columns 30–30, row 70 columns 31–31, row 70 columns 32–32, row 70 columns 33–33, row 70 columns 34–34, row 70
columns 35–35, row 70 columns 36–37, row 70 columns 38–39, row 70 columns 40–41), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1357 : rowsJ2 70 71 23 24 ≤ 0 := by decide +kernel

theorem rows22240R_1358 : rowsJ2 70 71 24 25 ≤ 0 := by decide +kernel

theorem rows22240R_1359 : rowsJ2 70 71 25 26 ≤ 0 := by decide +kernel

theorem rows22240R_1360 : rowsJ2 70 71 26 27 ≤ 0 := by decide +kernel

theorem rows22240R_1361 : rowsJ2 70 71 27 28 ≤ 0 := by decide +kernel

theorem rows22240R_1362 : rowsJ2 70 71 28 29 ≤ 0 := by decide +kernel

theorem rows22240R_1363 : rowsJ2 70 71 29 30 ≤ 0 := by decide +kernel

theorem rows22240R_1364 : rowsJ2 70 71 30 31 ≤ 0 := by decide +kernel

theorem rows22240R_1365 : rowsJ2 70 71 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_1366 : rowsJ2 70 71 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_1367 : rowsJ2 70 71 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_1368 : rowsJ2 70 71 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_1369 : rowsJ2 70 71 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_1370 : rowsJ2 70 71 36 38 ≤ 0 := by decide +kernel

theorem rows22240R_1371 : rowsJ2 70 71 38 40 ≤ 0 := by decide +kernel

theorem rows22240R_1372 : rowsJ2 70 71 40 42 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1357
#print axioms SieveCert.rows22240R_1372
