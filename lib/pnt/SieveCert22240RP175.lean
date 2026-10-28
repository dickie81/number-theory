/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1960–1973 of 5066

File 175 of 387: the parts `rows22240R_1960` … `rows22240R_1973` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 99914 in units of a depth-4 test: row 82 columns 51–51, row 82 columns
52–52, row 82 columns 53–53, row 82 columns 54–54, row 82 columns 55–55, row 82 columns 56–56, row 82 columns 57–57,
row 82 columns 58–58, row 82 columns 59–59, row 82 columns 60–60, row 82 columns 61–61, row 82 columns 62–62, row 82
columns 63–63, row 82 columns 64–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1960 : rowsJ2 82 83 51 52 ≤ 623484585395 := by decide +kernel

theorem rows22240R_1961 : rowsJ2 82 83 52 53 ≤ 568274759387 := by decide +kernel

theorem rows22240R_1962 : rowsJ2 82 83 53 54 ≤ 456639738641 := by decide +kernel

theorem rows22240R_1963 : rowsJ2 82 83 54 55 ≤ 400700661743 := by decide +kernel

theorem rows22240R_1964 : rowsJ2 82 83 55 56 ≤ 287454638201 := by decide +kernel

theorem rows22240R_1965 : rowsJ2 82 83 56 57 ≤ 230596995272 := by decide +kernel

theorem rows22240R_1966 : rowsJ2 82 83 57 58 ≤ 115492594670 := by decide +kernel

theorem rows22240R_1967 : rowsJ2 82 83 58 59 ≤ 57522618759 := by decide +kernel

theorem rows22240R_1968 : rowsJ2 82 83 59 60 ≤ 0 := by decide +kernel

theorem rows22240R_1969 : rowsJ2 82 83 60 61 ≤ 0 := by decide +kernel

theorem rows22240R_1970 : rowsJ2 82 83 61 62 ≤ 0 := by decide +kernel

theorem rows22240R_1971 : rowsJ2 82 83 62 63 ≤ 0 := by decide +kernel

theorem rows22240R_1972 : rowsJ2 82 83 63 64 ≤ 0 := by decide +kernel

theorem rows22240R_1973 : rowsJ2 82 83 64 65 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1960
#print axioms SieveCert.rows22240R_1973
