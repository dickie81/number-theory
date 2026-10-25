/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2851–2864 of 4715

File 227 of 351: the parts `rows22250R_2851` … `rows22250R_2864` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 94648 tests: row 106 columns 43–44, row 106 columns 45–47, row 106 columns
48–52, row 106 columns 53–63, row 106 columns 64–70, row 106 columns 71–74, row 106 columns 75–77, row 106 columns
78–79, row 106 columns 80–81, row 106 columns 82–83, row 106 columns 84–85, row 106 columns 86–87, row 106 columns
88–89, row 106 columns 90–91), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2851 : rowsJ2 106 107 43 45 ≤ 8688525602599 := by decide +kernel

theorem rows22250R_2852 : rowsJ2 106 107 45 48 ≤ 5981945849352 := by decide +kernel

theorem rows22250R_2853 : rowsJ2 106 107 48 53 ≤ 781601780259 := by decide +kernel

theorem rows22250R_2854 : rowsJ2 106 107 53 64 ≤ 25707558230 := by decide +kernel

theorem rows22250R_2855 : rowsJ2 106 107 64 71 ≤ 0 := by decide +kernel

theorem rows22250R_2856 : rowsJ2 106 107 71 75 ≤ 0 := by decide +kernel

theorem rows22250R_2857 : rowsJ2 106 107 75 78 ≤ 340931204830 := by decide +kernel

theorem rows22250R_2858 : rowsJ2 106 107 78 80 ≤ 1151878837906 := by decide +kernel

theorem rows22250R_2859 : rowsJ2 106 107 80 82 ≤ 1152004396833 := by decide +kernel

theorem rows22250R_2860 : rowsJ2 106 107 82 84 ≤ 916366074560 := by decide +kernel

theorem rows22250R_2861 : rowsJ2 106 107 84 86 ≤ 1219189587842 := by decide +kernel

theorem rows22250R_2862 : rowsJ2 106 107 86 88 ≤ 2127622530211 := by decide +kernel

theorem rows22250R_2863 : rowsJ2 106 107 88 90 ≤ 3667369802270 := by decide +kernel

theorem rows22250R_2864 : rowsJ2 106 107 90 92 ≤ 5866987960238 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2851
#print axioms SieveCert.rows22250R_2864
