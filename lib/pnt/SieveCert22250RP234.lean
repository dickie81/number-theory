/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2960–2973 of 4715

File 234 of 351: the parts `rows22250R_2960` … `rows22250R_2973` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 96888 in units of a depth-4 test: row 110 columns 0–26, row 110 columns
27–30, row 110 columns 31–32, row 110 columns 33–34, row 110 columns 35–36, row 110 columns 37–38, row 110 columns
39–40, row 110 columns 41–43, row 110 columns 44–48, row 110 columns 49–59, row 110 columns 60–66, row 110 columns
67–71, row 110 columns 72–75, row 110 columns 76–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2960 : rowsJ2 110 111 0 27 ≤ 468131084814 := by decide +kernel

theorem rows22250R_2961 : rowsJ2 110 111 27 31 ≤ 9417508006382 := by decide +kernel

theorem rows22250R_2962 : rowsJ2 110 111 31 33 ≤ 13135324636315 := by decide +kernel

theorem rows22250R_2963 : rowsJ2 110 111 33 35 ≤ 21449616127596 := by decide +kernel

theorem rows22250R_2964 : rowsJ2 110 111 35 37 ≤ 24285943752686 := by decide +kernel

theorem rows22250R_2965 : rowsJ2 110 111 37 39 ≤ 19166430394519 := by decide +kernel

theorem rows22250R_2966 : rowsJ2 110 111 39 41 ≤ 12619398544908 := by decide +kernel

theorem rows22250R_2967 : rowsJ2 110 111 41 44 ≤ 10184709701711 := by decide +kernel

theorem rows22250R_2968 : rowsJ2 110 111 44 49 ≤ 3795503892352 := by decide +kernel

theorem rows22250R_2969 : rowsJ2 110 111 49 60 ≤ 211671591383 := by decide +kernel

theorem rows22250R_2970 : rowsJ2 110 111 60 67 ≤ 1516478868545 := by decide +kernel

theorem rows22250R_2971 : rowsJ2 110 111 67 72 ≤ 0 := by decide +kernel

theorem rows22250R_2972 : rowsJ2 110 111 72 76 ≤ 14549950172 := by decide +kernel

theorem rows22250R_2973 : rowsJ2 110 111 76 78 ≤ 315204694393 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2960
#print axioms SieveCert.rows22250R_2973
