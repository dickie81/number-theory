/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2832–2848 of 5066

File 239 of 387: the parts `rows22240R_2832` … `rows22240R_2848` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 96181 in units of a depth-4 test: row 101 columns 86–86, row 101
columns 87–87, row 101 columns 88–88, row 101 columns 89–89, row 101 columns 90–90, row 101 columns 91–91, row 101
columns 92–92, row 101 columns 93–93, row 101 columns 94–94, row 101 columns 95–95, row 101 columns 96–96, row 101
columns 97–97, row 101 columns 98–98, row 101 columns 99–99, row 101 columns 100–100, row 101 columns 101–339, row
102 columns 0–16), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2832 : rowsJ2 101 102 86 87 ≤ 1706760607836 := by decide +kernel

theorem rows22240R_2833 : rowsJ2 101 102 87 88 ≤ 1816263511427 := by decide +kernel

theorem rows22240R_2834 : rowsJ2 101 102 88 89 ≤ 2024514435036 := by decide +kernel

theorem rows22240R_2835 : rowsJ2 101 102 89 90 ≤ 2273494546426 := by decide +kernel

theorem rows22240R_2836 : rowsJ2 101 102 90 91 ≤ 2624212369158 := by decide +kernel

theorem rows22240R_2837 : rowsJ2 101 102 91 92 ≤ 3017753864443 := by decide +kernel

theorem rows22240R_2838 : rowsJ2 101 102 92 93 ≤ 3516619460774 := by decide +kernel

theorem rows22240R_2839 : rowsJ2 101 102 93 94 ≤ 4061096437776 := by decide +kernel

theorem rows22240R_2840 : rowsJ2 101 102 94 95 ≤ 4715348500119 := by decide +kernel

theorem rows22240R_2841 : rowsJ2 101 102 95 96 ≤ 5418634862727 := by decide +kernel

theorem rows22240R_2842 : rowsJ2 101 102 96 97 ≤ 6236711693403 := by decide +kernel

theorem rows22240R_2843 : rowsJ2 101 102 97 98 ≤ 7107776020705 := by decide +kernel

theorem rows22240R_2844 : rowsJ2 101 102 98 99 ≤ 8099272708054 := by decide +kernel

theorem rows22240R_2845 : rowsJ2 101 102 99 100 ≤ 9148305113712 := by decide +kernel

theorem rows22240R_2846 : rowsJ2 101 102 100 101 ≤ 10324112106445 := by decide +kernel

theorem rows22240R_2847 : rowsJ2 101 102 101 340 ≤ 11562673914760 := by decide +kernel

theorem rows22240R_2848 : rowsJ2 102 103 0 17 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2832
#print axioms SieveCert.rows22240R_2848
