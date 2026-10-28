/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2865–2881 of 4715

File 228 of 351: the parts `rows22250R_2865` … `rows22250R_2881` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 97917 in units of a depth-4 test: row 106 columns 92–93, row 106
columns 94–95, row 106 columns 96–96, row 106 columns 97–97, row 106 columns 98–98, row 106 columns 99–99, row 106
columns 100–100, row 106 columns 101–339, row 107 columns 0–25, row 107 columns 26–30, row 107 columns 31–32, row
107 columns 33–34, row 107 columns 35–35, row 107 columns 36–36, row 107 columns 37–37, row 107 columns 38–39, row
107 columns 40–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2865 : rowsJ2 106 107 92 94 ≤ 8759628054126 := by decide +kernel

theorem rows22250R_2866 : rowsJ2 106 107 94 96 ≤ 12366805772821 := by decide +kernel

theorem rows22250R_2867 : rowsJ2 106 107 96 97 ≤ 7748627262601 := by decide +kernel

theorem rows22250R_2868 : rowsJ2 106 107 97 98 ≤ 8931917534284 := by decide +kernel

theorem rows22250R_2869 : rowsJ2 106 107 98 99 ≤ 10184468612449 := by decide +kernel

theorem rows22250R_2870 : rowsJ2 106 107 99 100 ≤ 11562573195704 := by decide +kernel

theorem rows22250R_2871 : rowsJ2 106 107 100 101 ≤ 13016082986481 := by decide +kernel

theorem rows22250R_2872 : rowsJ2 106 107 101 340 ≤ 604774991631360 := by decide +kernel

theorem rows22250R_2873 : rowsJ2 107 108 0 26 ≤ 0 := by decide +kernel

theorem rows22250R_2874 : rowsJ2 107 108 26 31 ≤ 6745540662310 := by decide +kernel

theorem rows22250R_2875 : rowsJ2 107 108 31 33 ≤ 10536421229904 := by decide +kernel

theorem rows22250R_2876 : rowsJ2 107 108 33 35 ≤ 17563488490409 := by decide +kernel

theorem rows22250R_2877 : rowsJ2 107 108 35 36 ≤ 12064925554963 := by decide +kernel

theorem rows22250R_2878 : rowsJ2 107 108 36 37 ≤ 14776034092085 := by decide +kernel

theorem rows22250R_2879 : rowsJ2 107 108 37 38 ≤ 13644259074578 := by decide +kernel

theorem rows22250R_2880 : rowsJ2 107 108 38 40 ≤ 21418770547567 := by decide +kernel

theorem rows22250R_2881 : rowsJ2 107 108 40 42 ≤ 14688717764676 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2865
#print axioms SieveCert.rows22250R_2881
