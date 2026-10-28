/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1823–1832 of 5066

File 165 of 387: the parts `rows22240R_1823` … `rows22240R_1832` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 93926 in units of a depth-4 test: row 79 columns 50–50, row 79 columns
51–51, row 79 columns 52–52, row 79 columns 53–53, row 79 columns 54–54, row 79 columns 55–55, row 79 columns 56–56,
row 79 columns 57–57, row 79 columns 58–58, row 79 columns 59–59), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1823 : rowsJ2 79 80 50 51 ≤ 1639018896824 := by decide +kernel

theorem rows22240R_1824 : rowsJ2 79 80 51 52 ≤ 1703045391400 := by decide +kernel

theorem rows22240R_1825 : rowsJ2 79 80 52 53 ≤ 1656063989150 := by decide +kernel

theorem rows22240R_1826 : rowsJ2 79 80 53 54 ≤ 1487808397572 := by decide +kernel

theorem rows22240R_1827 : rowsJ2 79 80 54 55 ≤ 1321371603542 := by decide +kernel

theorem rows22240R_1828 : rowsJ2 79 80 55 56 ≤ 1150957219219 := by decide +kernel

theorem rows22240R_1829 : rowsJ2 79 80 56 57 ≤ 982219217036 := by decide +kernel

theorem rows22240R_1830 : rowsJ2 79 80 57 58 ≤ 809213061120 := by decide +kernel

theorem rows22240R_1831 : rowsJ2 79 80 58 59 ≤ 637740660539 := by decide +kernel

theorem rows22240R_1832 : rowsJ2 79 80 59 60 ≤ 522819328666 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1823
#print axioms SieveCert.rows22240R_1832
