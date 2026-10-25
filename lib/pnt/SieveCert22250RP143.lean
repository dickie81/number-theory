/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1403–1418 of 5796

File 143 of 465: the parts `rows22250R_1403` … `rows22250R_1418` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97400 tests: row 71 columns 38–38, row 71 columns 39–39, row 71 columns
40–40, row 71 columns 41–41, row 71 columns 42–42, row 71 columns 43–43, row 71 columns 44–44, row 71 columns 45–45,
row 71 columns 46–46, row 71 columns 47–47, row 71 columns 48–48, row 71 columns 49–49, row 71 columns 50–50, row 71
columns 51–51, row 71 columns 52–52, row 71 columns 53–53), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1403 : rowsJ2 71 72 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_1404 : rowsJ2 71 72 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_1405 : rowsJ2 71 72 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_1406 : rowsJ2 71 72 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1407 : rowsJ2 71 72 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1408 : rowsJ2 71 72 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1409 : rowsJ2 71 72 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1410 : rowsJ2 71 72 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1411 : rowsJ2 71 72 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1412 : rowsJ2 71 72 47 48 ≤ 102233371665 := by decide +kernel

theorem rows22250R_1413 : rowsJ2 71 72 48 49 ≤ 458193507042 := by decide +kernel

theorem rows22250R_1414 : rowsJ2 71 72 49 50 ≤ 853216166987 := by decide +kernel

theorem rows22250R_1415 : rowsJ2 71 72 50 51 ≤ 1283262337090 := by decide +kernel

theorem rows22250R_1416 : rowsJ2 71 72 51 52 ≤ 1847251909246 := by decide +kernel

theorem rows22250R_1417 : rowsJ2 71 72 52 53 ≤ 2647497229421 := by decide +kernel

theorem rows22250R_1418 : rowsJ2 71 72 53 54 ≤ 3468429758464 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1403
#print axioms SieveCert.rows22250R_1418
