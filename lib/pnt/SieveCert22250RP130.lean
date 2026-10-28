/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1471–1483 of 4715

File 130 of 351: the parts `rows22250R_1471` … `rows22250R_1483` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 94575 in units of a depth-4 test: row 73 columns 39–40, row 73 columns
41–41, row 73 columns 42–42, row 73 columns 43–43, row 73 columns 44–44, row 73 columns 45–45, row 73 columns 46–46,
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

theorem rows22250R_1471 : rowsJ2 73 74 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1472 : rowsJ2 73 74 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1473 : rowsJ2 73 74 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1474 : rowsJ2 73 74 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1475 : rowsJ2 73 74 44 45 ≤ 61471012909 := by decide +kernel

theorem rows22250R_1476 : rowsJ2 73 74 45 46 ≤ 241273869947 := by decide +kernel

theorem rows22250R_1477 : rowsJ2 73 74 46 47 ≤ 719804080659 := by decide +kernel

theorem rows22250R_1478 : rowsJ2 73 74 47 48 ≤ 1429419250884 := by decide +kernel

theorem rows22250R_1479 : rowsJ2 73 74 48 49 ≤ 2112180951957 := by decide +kernel

theorem rows22250R_1480 : rowsJ2 73 74 49 50 ≤ 2685728985214 := by decide +kernel

theorem rows22250R_1481 : rowsJ2 73 74 50 51 ≤ 3274386594414 := by decide +kernel

theorem rows22250R_1482 : rowsJ2 73 74 51 52 ≤ 3825822490352 := by decide +kernel

theorem rows22250R_1483 : rowsJ2 73 74 52 53 ≤ 4133564311354 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1471
#print axioms SieveCert.rows22250R_1483
