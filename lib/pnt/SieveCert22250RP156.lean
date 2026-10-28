/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1828–1842 of 4715

File 156 of 351: the parts `rows22250R_1828` … `rows22250R_1842` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 99638 in units of a depth-4 test: row 81 columns 51–51, row 81 columns
52–52, row 81 columns 53–53, row 81 columns 54–54, row 81 columns 55–55, row 81 columns 56–56, row 81 columns 57–57,
row 81 columns 58–58, row 81 columns 59–59, row 81 columns 60–60, row 81 columns 61–61, row 81 columns 62–62, row 81
columns 63–63, row 81 columns 64–65, row 81 columns 66–67), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_1828 : rowsJ2 81 82 51 52 ≤ 582057689641 := by decide +kernel

theorem rows22250R_1829 : rowsJ2 81 82 52 53 ≤ 466141868329 := by decide +kernel

theorem rows22250R_1830 : rowsJ2 81 82 53 54 ≤ 351356349406 := by decide +kernel

theorem rows22250R_1831 : rowsJ2 81 82 54 55 ≤ 233666437900 := by decide +kernel

theorem rows22250R_1832 : rowsJ2 81 82 55 56 ≤ 117006024551 := by decide +kernel

theorem rows22250R_1833 : rowsJ2 81 82 56 57 ≤ 58266135778 := by decide +kernel

theorem rows22250R_1834 : rowsJ2 81 82 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_1835 : rowsJ2 81 82 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_1836 : rowsJ2 81 82 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_1837 : rowsJ2 81 82 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_1838 : rowsJ2 81 82 61 62 ≤ 0 := by decide +kernel

theorem rows22250R_1839 : rowsJ2 81 82 62 63 ≤ 0 := by decide +kernel

theorem rows22250R_1840 : rowsJ2 81 82 63 64 ≤ 0 := by decide +kernel

theorem rows22250R_1841 : rowsJ2 81 82 64 66 ≤ 0 := by decide +kernel

theorem rows22250R_1842 : rowsJ2 81 82 66 68 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1828
#print axioms SieveCert.rows22250R_1842
