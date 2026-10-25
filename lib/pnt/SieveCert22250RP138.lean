/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1345–1362 of 5796

File 138 of 465: the parts `rows22250R_1345` … `rows22250R_1362` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 96827 tests: row 70 columns 31–31, row 70 columns 32–32, row 70 columns
33–33, row 70 columns 34–34, row 70 columns 35–35, row 70 columns 36–36, row 70 columns 37–37, row 70 columns 38–38,
row 70 columns 39–39, row 70 columns 40–40, row 70 columns 41–41, row 70 columns 42–42, row 70 columns 43–43, row 70
columns 44–44, row 70 columns 45–45, row 70 columns 46–46, row 70 columns 47–47, row 70 columns 48–48), each a sum
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

theorem rows22250R_1345 : rowsJ2 70 71 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1346 : rowsJ2 70 71 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1347 : rowsJ2 70 71 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1348 : rowsJ2 70 71 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1349 : rowsJ2 70 71 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1350 : rowsJ2 70 71 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1351 : rowsJ2 70 71 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_1352 : rowsJ2 70 71 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_1353 : rowsJ2 70 71 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_1354 : rowsJ2 70 71 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_1355 : rowsJ2 70 71 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1356 : rowsJ2 70 71 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1357 : rowsJ2 70 71 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1358 : rowsJ2 70 71 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1359 : rowsJ2 70 71 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1360 : rowsJ2 70 71 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1361 : rowsJ2 70 71 47 48 ≤ 103086747659 := by decide +kernel

theorem rows22250R_1362 : rowsJ2 70 71 48 49 ≤ 462018200811 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1345
#print axioms SieveCert.rows22250R_1362
