/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3081–3097 of 5066

File 254 of 387: the parts `rows22240R_3081` … `rows22240R_3097` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 98447 in units of a depth-4 test: row 107 columns 75–77, row 107
columns 78–79, row 107 columns 80–80, row 107 columns 81–82, row 107 columns 83–84, row 107 columns 85–86, row 107
columns 87–88, row 107 columns 89–90, row 107 columns 91–92, row 107 columns 93–93, row 107 columns 94–94, row 107
columns 95–95, row 107 columns 96–96, row 107 columns 97–97, row 107 columns 98–98, row 107 columns 99–99, row 107
columns 100–100), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3081 : rowsJ2 107 108 75 78 ≤ 216932017046 := by decide +kernel

theorem rows22240R_3082 : rowsJ2 107 108 78 80 ≤ 906053204370 := by decide +kernel

theorem rows22240R_3083 : rowsJ2 107 108 80 81 ≤ 665585631543 := by decide +kernel

theorem rows22240R_3084 : rowsJ2 107 108 81 83 ≤ 1159881593479 := by decide +kernel

theorem rows22240R_3085 : rowsJ2 107 108 83 85 ≤ 1426311422538 := by decide +kernel

theorem rows22240R_3086 : rowsJ2 107 108 85 87 ≤ 2279132007110 := by decide +kernel

theorem rows22240R_3087 : rowsJ2 107 108 87 89 ≤ 3740708444269 := by decide +kernel

theorem rows22240R_3088 : rowsJ2 107 108 89 91 ≤ 5839125909797 := by decide +kernel

theorem rows22240R_3089 : rowsJ2 107 108 91 93 ≤ 8606930487166 := by decide +kernel

theorem rows22240R_3090 : rowsJ2 107 108 93 94 ≤ 5552440335092 := by decide +kernel

theorem rows22240R_3091 : rowsJ2 107 108 94 95 ≤ 6529000140699 := by decide +kernel

theorem rows22240R_3092 : rowsJ2 107 108 95 96 ≤ 7567623868470 := by decide +kernel

theorem rows22240R_3093 : rowsJ2 107 108 96 97 ≤ 8721492881655 := by decide +kernel

theorem rows22240R_3094 : rowsJ2 107 108 97 98 ≤ 9942492147010 := by decide +kernel

theorem rows22240R_3095 : rowsJ2 107 108 98 99 ≤ 11285483723758 := by decide +kernel

theorem rows22240R_3096 : rowsJ2 107 108 99 100 ≤ 12701468665935 := by decide +kernel

theorem rows22240R_3097 : rowsJ2 107 108 100 101 ≤ 14247115853673 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3081
#print axioms SieveCert.rows22240R_3097
