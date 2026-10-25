/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1816–1829 of 5796

File 178 of 465: the parts `rows22250R_1816` … `rows22250R_1829` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 93636 tests: row 79 columns 30–31, row 79 columns 32–33, row 79 columns
34–35, row 79 columns 36–37, row 79 columns 38–39, row 79 columns 40–41, row 79 columns 42–43, row 79 columns 44–44,
row 79 columns 45–45, row 79 columns 46–46, row 79 columns 47–47, row 79 columns 48–48, row 79 columns 49–49, row 79
columns 50–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1816 : rowsJ2 79 80 30 32 ≤ 0 := by decide +kernel

theorem rows22250R_1817 : rowsJ2 79 80 32 34 ≤ 0 := by decide +kernel

theorem rows22250R_1818 : rowsJ2 79 80 34 36 ≤ 0 := by decide +kernel

theorem rows22250R_1819 : rowsJ2 79 80 36 38 ≤ 0 := by decide +kernel

theorem rows22250R_1820 : rowsJ2 79 80 38 40 ≤ 0 := by decide +kernel

theorem rows22250R_1821 : rowsJ2 79 80 40 42 ≤ 0 := by decide +kernel

theorem rows22250R_1822 : rowsJ2 79 80 42 44 ≤ 0 := by decide +kernel

theorem rows22250R_1823 : rowsJ2 79 80 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1824 : rowsJ2 79 80 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1825 : rowsJ2 79 80 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1826 : rowsJ2 79 80 47 48 ≤ 95883410846 := by decide +kernel

theorem rows22250R_1827 : rowsJ2 79 80 48 49 ≤ 429734005318 := by decide +kernel

theorem rows22250R_1828 : rowsJ2 79 80 49 50 ≤ 800220856923 := by decide +kernel

theorem rows22250R_1829 : rowsJ2 79 80 50 51 ≤ 1203555824158 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1816
#print axioms SieveCert.rows22250R_1829
