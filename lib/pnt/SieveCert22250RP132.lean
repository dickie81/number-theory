/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1494–1510 of 4715

File 132 of 351: the parts `rows22250R_1494` … `rows22250R_1510` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 97373 in units of a depth-4 test: row 73 columns 63–63, row 73 columns
64–64, row 73 columns 65–65, row 73 columns 66–66, row 73 columns 67–67, row 73 columns 68–68, row 73 columns 69–69,
row 73 columns 70–70, row 73 columns 71–71, row 73 columns 72–339, row 74 columns 0–17, row 74 columns 18–19, row 74
columns 20–21, row 74 columns 22–22, row 74 columns 23–23, row 74 columns 24–24, row 74 columns 25–25), each a sum
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

theorem rows22250R_1494 : rowsJ2 73 74 63 64 ≤ 1598586694011 := by decide +kernel

theorem rows22250R_1495 : rowsJ2 73 74 64 65 ≤ 1356351963199 := by decide +kernel

theorem rows22250R_1496 : rowsJ2 73 74 65 66 ≤ 1115944339721 := by decide +kernel

theorem rows22250R_1497 : rowsJ2 73 74 66 67 ≤ 868535159646 := by decide +kernel

theorem rows22250R_1498 : rowsJ2 73 74 67 68 ≤ 622760674363 := by decide +kernel

theorem rows22250R_1499 : rowsJ2 73 74 68 69 ≤ 436823603111 := by decide +kernel

theorem rows22250R_1500 : rowsJ2 73 74 69 70 ≤ 251995649580 := by decide +kernel

theorem rows22250R_1501 : rowsJ2 73 74 70 71 ≤ 127564432412 := by decide +kernel

theorem rows22250R_1502 : rowsJ2 73 74 71 72 ≤ 64788357587 := by decide +kernel

theorem rows22250R_1503 : rowsJ2 73 74 72 340 ≤ 0 := by decide +kernel

theorem rows22250R_1504 : rowsJ2 74 75 0 18 ≤ 438268149103 := by decide +kernel

theorem rows22250R_1505 : rowsJ2 74 75 18 20 ≤ 4022971469 := by decide +kernel

theorem rows22250R_1506 : rowsJ2 74 75 20 22 ≤ 7278385931 := by decide +kernel

theorem rows22250R_1507 : rowsJ2 74 75 22 23 ≤ 2122188111 := by decide +kernel

theorem rows22250R_1508 : rowsJ2 74 75 23 24 ≤ 2124303110 := by decide +kernel

theorem rows22250R_1509 : rowsJ2 74 75 24 25 ≤ 1063682419 := by decide +kernel

theorem rows22250R_1510 : rowsJ2 74 75 25 26 ≤ 1065556609 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1494
#print axioms SieveCert.rows22250R_1510
