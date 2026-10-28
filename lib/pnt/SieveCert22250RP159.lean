/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1871–1885 of 4715

File 159 of 351: the parts `rows22250R_1871` … `rows22250R_1885` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 94710 in units of a depth-4 test: row 82 columns 52–52, row 82 columns
53–53, row 82 columns 54–54, row 82 columns 55–55, row 82 columns 56–56, row 82 columns 57–57, row 82 columns 58–58,
row 82 columns 59–59, row 82 columns 60–60, row 82 columns 61–61, row 82 columns 62–62, row 82 columns 63–64, row 82
columns 65–66, row 82 columns 67–68, row 82 columns 69–71), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_1871 : rowsJ2 82 83 52 53 ≤ 292003984156 := by decide +kernel

theorem rows22250R_1872 : rowsJ2 82 83 53 54 ≤ 234173331561 := by decide +kernel

theorem rows22250R_1873 : rowsJ2 82 83 54 55 ≤ 117248358627 := by decide +kernel

theorem rows22250R_1874 : rowsJ2 82 83 55 56 ≤ 58381203793 := by decide +kernel

theorem rows22250R_1875 : rowsJ2 82 83 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_1876 : rowsJ2 82 83 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_1877 : rowsJ2 82 83 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_1878 : rowsJ2 82 83 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_1879 : rowsJ2 82 83 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_1880 : rowsJ2 82 83 61 62 ≤ 0 := by decide +kernel

theorem rows22250R_1881 : rowsJ2 82 83 62 63 ≤ 0 := by decide +kernel

theorem rows22250R_1882 : rowsJ2 82 83 63 65 ≤ 0 := by decide +kernel

theorem rows22250R_1883 : rowsJ2 82 83 65 67 ≤ 0 := by decide +kernel

theorem rows22250R_1884 : rowsJ2 82 83 67 69 ≤ 0 := by decide +kernel

theorem rows22250R_1885 : rowsJ2 82 83 69 72 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1871
#print axioms SieveCert.rows22250R_1885
