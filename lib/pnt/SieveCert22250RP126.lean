/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1415–1431 of 4715

File 126 of 351: the parts `rows22250R_1415` … `rows22250R_1431` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 99632 tests: row 72 columns 24–24, row 72 columns 25–25, row 72 columns
26–26, row 72 columns 27–27, row 72 columns 28–28, row 72 columns 29–30, row 72 columns 31–32, row 72 columns 33–34,
row 72 columns 35–36, row 72 columns 37–38, row 72 columns 39–40, row 72 columns 41–42, row 72 columns 43–43, row 72
columns 44–44, row 72 columns 45–45, row 72 columns 46–46, row 72 columns 47–47), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1415 : rowsJ2 72 73 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1416 : rowsJ2 72 73 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1417 : rowsJ2 72 73 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1418 : rowsJ2 72 73 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1419 : rowsJ2 72 73 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1420 : rowsJ2 72 73 29 31 ≤ 0 := by decide +kernel

theorem rows22250R_1421 : rowsJ2 72 73 31 33 ≤ 0 := by decide +kernel

theorem rows22250R_1422 : rowsJ2 72 73 33 35 ≤ 0 := by decide +kernel

theorem rows22250R_1423 : rowsJ2 72 73 35 37 ≤ 0 := by decide +kernel

theorem rows22250R_1424 : rowsJ2 72 73 37 39 ≤ 0 := by decide +kernel

theorem rows22250R_1425 : rowsJ2 72 73 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1426 : rowsJ2 72 73 41 43 ≤ 0 := by decide +kernel

theorem rows22250R_1427 : rowsJ2 72 73 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1428 : rowsJ2 72 73 44 45 ≤ 61987436537 := by decide +kernel

theorem rows22250R_1429 : rowsJ2 72 73 45 46 ≤ 243300833899 := by decide +kernel

theorem rows22250R_1430 : rowsJ2 72 73 46 47 ≤ 725851220884 := by decide +kernel

theorem rows22250R_1431 : rowsJ2 72 73 47 48 ≤ 1441427933361 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1415
#print axioms SieveCert.rows22250R_1431
