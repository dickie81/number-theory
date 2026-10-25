/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1815–1827 of 4715

File 155 of 351: the parts `rows22250R_1815` … `rows22250R_1827` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 95571 tests: row 81 columns 32–35, row 81 columns 36–38, row 81 columns
39–40, row 81 columns 41–41, row 81 columns 42–42, row 81 columns 43–43, row 81 columns 44–44, row 81 columns 45–45,
row 81 columns 46–46, row 81 columns 47–47, row 81 columns 48–48, row 81 columns 49–49, row 81 columns 50–50), each
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

theorem rows22250R_1815 : rowsJ2 81 82 32 36 ≤ 1896678035672 := by decide +kernel

theorem rows22250R_1816 : rowsJ2 81 82 36 39 ≤ 8448214366741 := by decide +kernel

theorem rows22250R_1817 : rowsJ2 81 82 39 41 ≤ 4516650481130 := by decide +kernel

theorem rows22250R_1818 : rowsJ2 81 82 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1819 : rowsJ2 81 82 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1820 : rowsJ2 81 82 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1821 : rowsJ2 81 82 44 45 ≤ 57630039239 := by decide +kernel

theorem rows22250R_1822 : rowsJ2 81 82 45 46 ≤ 226198039279 := by decide +kernel

theorem rows22250R_1823 : rowsJ2 81 82 46 47 ≤ 568009550442 := by decide +kernel

theorem rows22250R_1824 : rowsJ2 81 82 47 48 ≤ 861428782078 := by decide +kernel

theorem rows22250R_1825 : rowsJ2 81 82 48 49 ≤ 921641092147 := by decide +kernel

theorem rows22250R_1826 : rowsJ2 81 82 49 50 ≤ 809710372929 := by decide +kernel

theorem rows22250R_1827 : rowsJ2 81 82 50 51 ≤ 695268488297 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1815
#print axioms SieveCert.rows22250R_1827
