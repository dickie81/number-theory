/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2834–2850 of 4715

File 226 of 351: the parts `rows22250R_2834` … `rows22250R_2850` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 95168 tests: row 105 columns 94–95, row 105 columns 96–96, row 105 columns
97–97, row 105 columns 98–98, row 105 columns 99–99, row 105 columns 100–100, row 105 columns 101–339, row 106
columns 0–24, row 106 columns 25–30, row 106 columns 31–32, row 106 columns 33–34, row 106 columns 35–35, row 106
columns 36–36, row 106 columns 37–37, row 106 columns 38–38, row 106 columns 39–40, row 106 columns 41–42), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22250R_2834 : rowsJ2 105 106 94 96 ≤ 11546436387315 := by decide +kernel

theorem rows22250R_2835 : rowsJ2 105 106 96 97 ≤ 7283483192348 := by decide +kernel

theorem rows22250R_2836 : rowsJ2 105 106 97 98 ≤ 8392114778449 := by decide +kernel

theorem rows22250R_2837 : rowsJ2 105 106 98 99 ≤ 9619583499526 := by decide +kernel

theorem rows22250R_2838 : rowsJ2 105 106 99 100 ≤ 10916727097514 := by decide +kernel

theorem rows22250R_2839 : rowsJ2 105 106 100 101 ≤ 12339868499780 := by decide +kernel

theorem rows22250R_2840 : rowsJ2 105 106 101 340 ≤ 501177689659201 := by decide +kernel

theorem rows22250R_2841 : rowsJ2 106 107 0 25 ≤ 0 := by decide +kernel

theorem rows22250R_2842 : rowsJ2 106 107 25 31 ≤ 5857051418573 := by decide +kernel

theorem rows22250R_2843 : rowsJ2 106 107 31 33 ≤ 9673548377802 := by decide +kernel

theorem rows22250R_2844 : rowsJ2 106 107 33 35 ≤ 16628712592959 := by decide +kernel

theorem rows22250R_2845 : rowsJ2 106 107 35 36 ≤ 11322573137143 := by decide +kernel

theorem rows22250R_2846 : rowsJ2 106 107 36 37 ≤ 13928202165613 := by decide +kernel

theorem rows22250R_2847 : rowsJ2 106 107 37 38 ≤ 14695602290240 := by decide +kernel

theorem rows22250R_2848 : rowsJ2 106 107 38 39 ≤ 12637497841226 := by decide +kernel

theorem rows22250R_2849 : rowsJ2 106 107 39 41 ≤ 19591134835887 := by decide +kernel

theorem rows22250R_2850 : rowsJ2 106 107 41 43 ≤ 13394163595847 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2834
#print axioms SieveCert.rows22250R_2850
