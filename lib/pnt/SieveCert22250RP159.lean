/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1580–1589 of 5796

File 159 of 465: the parts `rows22250R_1580` … `rows22250R_1589` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 93379 tests: row 74 columns 64–64, row 74 columns 65–65, row 74 columns
66–66, row 74 columns 67–67, row 74 columns 68–68, row 74 columns 69–69, row 74 columns 70–70, row 74 columns 71–71,
row 74 columns 72–72, row 74 columns 73–73), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1580 : rowsJ2 74 75 64 65 ≤ 3631066052130 := by decide +kernel

theorem rows22250R_1581 : rowsJ2 74 75 65 66 ≤ 3301810320217 := by decide +kernel

theorem rows22250R_1582 : rowsJ2 74 75 66 67 ≤ 3018377246639 := by decide +kernel

theorem rows22250R_1583 : rowsJ2 74 75 67 68 ≤ 2737340839472 := by decide +kernel

theorem rows22250R_1584 : rowsJ2 74 75 68 69 ≤ 2502235146099 := by decide +kernel

theorem rows22250R_1585 : rowsJ2 74 75 69 70 ≤ 2269042688722 := by decide +kernel

theorem rows22250R_1586 : rowsJ2 74 75 70 71 ≤ 2081982354923 := by decide +kernel

theorem rows22250R_1587 : rowsJ2 74 75 71 72 ≤ 1844588040710 := by decide +kernel

theorem rows22250R_1588 : rowsJ2 74 75 72 73 ≤ 1653878414556 := by decide +kernel

theorem rows22250R_1589 : rowsJ2 74 75 73 74 ≤ 1411774263465 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1580
#print axioms SieveCert.rows22250R_1589
