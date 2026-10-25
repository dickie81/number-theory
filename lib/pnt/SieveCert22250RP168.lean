/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1685–1697 of 5796

File 168 of 465: the parts `rows22250R_1685` … `rows22250R_1697` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 99512 tests: row 76 columns 65–65, row 76 columns 66–66, row 76 columns
67–67, row 76 columns 68–68, row 76 columns 69–69, row 76 columns 70–70, row 76 columns 71–71, row 76 columns 72–72,
row 76 columns 73–73, row 76 columns 74–74, row 76 columns 75–75, row 76 columns 76–359, row 77 columns 0–18), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1685 : rowsJ2 76 77 65 66 ≤ 2324852226120 := by decide +kernel

theorem rows22250R_1686 : rowsJ2 76 77 66 67 ≤ 2088231390242 := by decide +kernel

theorem rows22250R_1687 : rowsJ2 76 77 67 68 ≤ 1853519566769 := by decide +kernel

theorem rows22250R_1688 : rowsJ2 76 77 68 69 ≤ 1664967637501 := by decide +kernel

theorem rows22250R_1689 : rowsJ2 76 77 69 70 ≤ 1477876266710 := by decide +kernel

theorem rows22250R_1690 : rowsJ2 76 77 70 71 ≤ 1337206706588 := by decide +kernel

theorem rows22250R_1691 : rowsJ2 76 77 71 72 ≤ 1146608535367 := by decide +kernel

theorem rows22250R_1692 : rowsJ2 76 77 72 73 ≤ 1003041915374 := by decide +kernel

theorem rows22250R_1693 : rowsJ2 76 77 73 74 ≤ 808530709987 := by decide +kernel

theorem rows22250R_1694 : rowsJ2 76 77 74 75 ≤ 661698436394 := by decide +kernel

theorem rows22250R_1695 : rowsJ2 76 77 75 76 ≤ 462850884291 := by decide +kernel

theorem rows22250R_1696 : rowsJ2 76 77 76 360 ≤ 312367942225 := by decide +kernel

theorem rows22250R_1697 : rowsJ2 77 78 0 19 ≤ 448413032880 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1685
#print axioms SieveCert.rows22250R_1697
