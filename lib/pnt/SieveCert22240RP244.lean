/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2915–2933 of 5066

File 244 of 387: the parts `rows22240R_2915` … `rows22240R_2933` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (19 parts, work 95611 in units of a depth-4 test: row 103 columns 73–76, row 103
columns 77–78, row 103 columns 79–79, row 103 columns 80–80, row 103 columns 81–81, row 103 columns 82–82, row 103
columns 83–83, row 103 columns 84–84, row 103 columns 85–85, row 103 columns 86–86, row 103 columns 87–87, row 103
columns 88–88, row 103 columns 89–89, row 103 columns 90–90, row 103 columns 91–91, row 103 columns 92–92, row 103
columns 93–93, row 103 columns 94–94, row 103 columns 95–95), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2915 : rowsJ2 103 104 73 77 ≤ 56504226358 := by decide +kernel

theorem rows22240R_2916 : rowsJ2 103 104 77 79 ≤ 519254752234 := by decide +kernel

theorem rows22240R_2917 : rowsJ2 103 104 79 80 ≤ 587574577115 := by decide +kernel

theorem rows22240R_2918 : rowsJ2 103 104 80 81 ≤ 895014063624 := by decide +kernel

theorem rows22240R_2919 : rowsJ2 103 104 81 82 ≤ 1258758777374 := by decide +kernel

theorem rows22240R_2920 : rowsJ2 103 104 82 83 ≤ 1405075614228 := by decide +kernel

theorem rows22240R_2921 : rowsJ2 103 104 83 84 ≤ 1275009555411 := by decide +kernel

theorem rows22240R_2922 : rowsJ2 103 104 84 85 ≤ 1239547498026 := by decide +kernel

theorem rows22240R_2923 : rowsJ2 103 104 85 86 ≤ 1285583442323 := by decide +kernel

theorem rows22240R_2924 : rowsJ2 103 104 86 87 ≤ 1430506397520 := by decide +kernel

theorem rows22240R_2925 : rowsJ2 103 104 87 88 ≤ 1616663413676 := by decide +kernel

theorem rows22240R_2926 : rowsJ2 103 104 88 89 ≤ 1904558133715 := by decide +kernel

theorem rows22240R_2927 : rowsJ2 103 104 89 90 ≤ 2235658613496 := by decide +kernel

theorem rows22240R_2928 : rowsJ2 103 104 90 91 ≤ 2671943453480 := by decide +kernel

theorem rows22240R_2929 : rowsJ2 103 104 91 92 ≤ 3154098083094 := by decide +kernel

theorem rows22240R_2930 : rowsJ2 103 104 92 93 ≤ 3745746325409 := by decide +kernel

theorem rows22240R_2931 : rowsJ2 103 104 93 94 ≤ 4386560685893 := by decide +kernel

theorem rows22240R_2932 : rowsJ2 103 104 94 95 ≤ 5141738441271 := by decide +kernel

theorem rows22240R_2933 : rowsJ2 103 104 95 96 ≤ 5949905058850 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2915
#print axioms SieveCert.rows22240R_2933
