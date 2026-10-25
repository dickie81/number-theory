/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1504–1517 of 5796

File 152 of 465: the parts `rows22250R_1504` … `rows22250R_1517` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 94063 tests: row 73 columns 36–36, row 73 columns 37–38, row 73 columns
39–40, row 73 columns 41–42, row 73 columns 43–43, row 73 columns 44–44, row 73 columns 45–45, row 73 columns 46–46,
row 73 columns 47–47, row 73 columns 48–48, row 73 columns 49–49, row 73 columns 50–50, row 73 columns 51–51, row 73
columns 52–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1504 : rowsJ2 73 74 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1505 : rowsJ2 73 74 37 39 ≤ 0 := by decide +kernel

theorem rows22250R_1506 : rowsJ2 73 74 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1507 : rowsJ2 73 74 41 43 ≤ 0 := by decide +kernel

theorem rows22250R_1508 : rowsJ2 73 74 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1509 : rowsJ2 73 74 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1510 : rowsJ2 73 74 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1511 : rowsJ2 73 74 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1512 : rowsJ2 73 74 47 48 ≤ 100568315998 := by decide +kernel

theorem rows22250R_1513 : rowsJ2 73 74 48 49 ≤ 450730995703 := by decide +kernel

theorem rows22250R_1514 : rowsJ2 73 74 49 50 ≤ 839319995995 := by decide +kernel

theorem rows22250R_1515 : rowsJ2 73 74 50 51 ≤ 1262362085137 := by decide +kernel

theorem rows22250R_1516 : rowsJ2 73 74 51 52 ≤ 1817166065371 := by decide +kernel

theorem rows22250R_1517 : rowsJ2 73 74 52 53 ≤ 2604377940757 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1504
#print axioms SieveCert.rows22250R_1517
