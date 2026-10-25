/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1535–1549 of 4715

File 135 of 351: the parts `rows22250R_1535` … `rows22250R_1549` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99638 tests: row 74 columns 58–58, row 74 columns 59–59, row 74 columns
60–60, row 74 columns 61–61, row 74 columns 62–62, row 74 columns 63–63, row 74 columns 64–64, row 74 columns 65–65,
row 74 columns 66–66, row 74 columns 67–67, row 74 columns 68–68, row 74 columns 69–69, row 74 columns 70–70, row 74
columns 71–72, row 74 columns 73–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1535 : rowsJ2 74 75 58 59 ≤ 2222239718976 := by decide +kernel

theorem rows22250R_1536 : rowsJ2 74 75 59 60 ≤ 2050161087526 := by decide +kernel

theorem rows22250R_1537 : rowsJ2 74 75 60 61 ≤ 1817676458152 := by decide +kernel

theorem rows22250R_1538 : rowsJ2 74 75 61 62 ≤ 1642808767193 := by decide +kernel

theorem rows22250R_1539 : rowsJ2 74 75 62 63 ≤ 1406339221713 := by decide +kernel

theorem rows22250R_1540 : rowsJ2 74 75 63 64 ≤ 1228191591866 := by decide +kernel

theorem rows22250R_1541 : rowsJ2 74 75 64 65 ≤ 987177587667 := by decide +kernel

theorem rows22250R_1542 : rowsJ2 74 75 65 66 ≤ 805242423928 := by decide +kernel

theorem rows22250R_1543 : rowsJ2 74 75 66 67 ≤ 559103566132 := by decide +kernel

theorem rows22250R_1544 : rowsJ2 74 75 67 68 ≤ 372853003987 := by decide +kernel

theorem rows22250R_1545 : rowsJ2 74 75 68 69 ≤ 187726523082 := by decide +kernel

theorem rows22250R_1546 : rowsJ2 74 75 69 70 ≤ 63027374706 := by decide +kernel

theorem rows22250R_1547 : rowsJ2 74 75 70 71 ≤ 0 := by decide +kernel

theorem rows22250R_1548 : rowsJ2 74 75 71 73 ≤ 0 := by decide +kernel

theorem rows22250R_1549 : rowsJ2 74 75 73 340 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1535
#print axioms SieveCert.rows22250R_1549
