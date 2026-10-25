/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1866–1880 of 5796

File 182 of 465: the parts `rows22250R_1866` … `rows22250R_1880` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 96070 tests: row 80 columns 27–27, row 80 columns 28–28, row 80 columns
29–30, row 80 columns 31–32, row 80 columns 33–34, row 80 columns 35–37, row 80 columns 38–39, row 80 columns 40–41,
row 80 columns 42–43, row 80 columns 44–44, row 80 columns 45–45, row 80 columns 46–46, row 80 columns 47–47, row 80
columns 48–48, row 80 columns 49–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1866 : rowsJ2 80 81 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1867 : rowsJ2 80 81 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1868 : rowsJ2 80 81 29 31 ≤ 0 := by decide +kernel

theorem rows22250R_1869 : rowsJ2 80 81 31 33 ≤ 0 := by decide +kernel

theorem rows22250R_1870 : rowsJ2 80 81 33 35 ≤ 0 := by decide +kernel

theorem rows22250R_1871 : rowsJ2 80 81 35 38 ≤ 0 := by decide +kernel

theorem rows22250R_1872 : rowsJ2 80 81 38 40 ≤ 0 := by decide +kernel

theorem rows22250R_1873 : rowsJ2 80 81 40 42 ≤ 0 := by decide +kernel

theorem rows22250R_1874 : rowsJ2 80 81 42 44 ≤ 0 := by decide +kernel

theorem rows22250R_1875 : rowsJ2 80 81 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1876 : rowsJ2 80 81 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1877 : rowsJ2 80 81 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1878 : rowsJ2 80 81 47 48 ≤ 95144702531 := by decide +kernel

theorem rows22250R_1879 : rowsJ2 80 81 48 49 ≤ 426423233623 := by decide +kernel

theorem rows22250R_1880 : rowsJ2 80 81 49 50 ≤ 794055767516 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1866
#print axioms SieveCert.rows22250R_1880
