/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1385–1392 of 5066

File 132 of 387: the parts `rows22240R_1385` … `rows22240R_1392` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (8 parts, work 96111 in units of a depth-4 test: row 70 columns 54–54, row 70 columns
55–55, row 70 columns 56–56, row 70 columns 57–57, row 70 columns 58–58, row 70 columns 59–59, row 70 columns 60–60,
row 70 columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1385 : rowsJ2 70 71 54 55 ≤ 5940546558330 := by decide +kernel

theorem rows22240R_1386 : rowsJ2 70 71 55 56 ≤ 6320946595864 := by decide +kernel

theorem rows22240R_1387 : rowsJ2 70 71 56 57 ≤ 6780788554852 := by decide +kernel

theorem rows22240R_1388 : rowsJ2 70 71 57 58 ≤ 6324406066918 := by decide +kernel

theorem rows22240R_1389 : rowsJ2 70 71 58 59 ≤ 5923839175124 := by decide +kernel

theorem rows22240R_1390 : rowsJ2 70 71 59 60 ≤ 5527669608649 := by decide +kernel

theorem rows22240R_1391 : rowsJ2 70 71 60 61 ≤ 5187191652233 := by decide +kernel

theorem rows22240R_1392 : rowsJ2 70 71 61 62 ≤ 4850355699865 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1385
#print axioms SieveCert.rows22240R_1392
