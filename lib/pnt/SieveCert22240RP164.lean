/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1809–1822 of 5066

File 164 of 387: the parts `rows22240R_1809` … `rows22240R_1822` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 93121 in units of a depth-4 test: row 79 columns 29–30, row 79 columns
31–33, row 79 columns 34–36, row 79 columns 37–38, row 79 columns 39–40, row 79 columns 41–41, row 79 columns 42–42,
row 79 columns 43–43, row 79 columns 44–44, row 79 columns 45–45, row 79 columns 46–46, row 79 columns 47–47, row 79
columns 48–48, row 79 columns 49–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_1809 : rowsJ2 79 80 29 31 ≤ 0 := by decide +kernel

theorem rows22240R_1810 : rowsJ2 79 80 31 34 ≤ 0 := by decide +kernel

theorem rows22240R_1811 : rowsJ2 79 80 34 37 ≤ 1587532884129 := by decide +kernel

theorem rows22240R_1812 : rowsJ2 79 80 37 39 ≤ 2693041261837 := by decide +kernel

theorem rows22240R_1813 : rowsJ2 79 80 39 41 ≤ 872951794330 := by decide +kernel

theorem rows22240R_1814 : rowsJ2 79 80 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1815 : rowsJ2 79 80 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1816 : rowsJ2 79 80 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1817 : rowsJ2 79 80 44 45 ≤ 59382858791 := by decide +kernel

theorem rows22240R_1818 : rowsJ2 79 80 45 46 ≤ 173661733132 := by decide +kernel

theorem rows22240R_1819 : rowsJ2 79 80 46 47 ≤ 338664715800 := by decide +kernel

theorem rows22240R_1820 : rowsJ2 79 80 47 48 ≤ 723077337481 := by decide +kernel

theorem rows22240R_1821 : rowsJ2 79 80 48 49 ≤ 1176718991082 := by decide +kernel

theorem rows22240R_1822 : rowsJ2 79 80 49 50 ≤ 1519528448187 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1809
#print axioms SieveCert.rows22240R_1822
