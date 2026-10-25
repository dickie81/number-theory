/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1838–1847 of 5796

File 180 of 465: the parts `rows22250R_1838` … `rows22250R_1847` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 93379 tests: row 79 columns 59–59, row 79 columns 60–60, row 79 columns
61–61, row 79 columns 62–62, row 79 columns 63–63, row 79 columns 64–64, row 79 columns 65–65, row 79 columns 66–66,
row 79 columns 67–67, row 79 columns 68–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1838 : rowsJ2 79 80 59 60 ≤ 2167907488675 := by decide +kernel

theorem rows22250R_1839 : rowsJ2 79 80 60 61 ≤ 1987427456712 := by decide +kernel

theorem rows22250R_1840 : rowsJ2 79 80 61 62 ≤ 1802782793115 := by decide +kernel

theorem rows22250R_1841 : rowsJ2 79 80 62 63 ≤ 1619839547568 := by decide +kernel

theorem rows22250R_1842 : rowsJ2 79 80 63 64 ≤ 1432449659777 := by decide +kernel

theorem rows22250R_1843 : rowsJ2 79 80 64 65 ≤ 1246628505802 := by decide +kernel

theorem rows22250R_1844 : rowsJ2 79 80 65 66 ≤ 1056068876891 := by decide +kernel

theorem rows22250R_1845 : rowsJ2 79 80 66 67 ≤ 866943647682 := by decide +kernel

theorem rows22250R_1846 : rowsJ2 79 80 67 68 ≤ 724290013165 := by decide +kernel

theorem rows22250R_1847 : rowsJ2 79 80 68 69 ≤ 582647572518 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1838
#print axioms SieveCert.rows22250R_1847
