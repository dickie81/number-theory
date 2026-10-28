/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 792–802 of 4715

File 75 of 351: the parts `rows22250R_792` … `rows22250R_802` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, work 94410 in units of a depth-4 test: row 57 columns 54–54, row 57 columns
55–55, row 57 columns 56–56, row 57 columns 57–339, row 58 columns 0–16, row 58 columns 17–20, row 58 columns 21–22,
row 58 columns 23–23, row 58 columns 24–24, row 58 columns 25–25, row 58 columns 26–26), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_792 : rowsJ2 57 58 54 55 ≤ 10179950081695 := by decide +kernel

theorem rows22250R_793 : rowsJ2 57 58 55 56 ≤ 11732778458420 := by decide +kernel

theorem rows22250R_794 : rowsJ2 57 58 56 57 ≤ 13100851537064 := by decide +kernel

theorem rows22250R_795 : rowsJ2 57 58 57 340 ≤ 14310630342497 := by decide +kernel

theorem rows22250R_796 : rowsJ2 58 59 0 17 ≤ 2793989972600 := by decide +kernel

theorem rows22250R_797 : rowsJ2 58 59 17 21 ≤ 508982807561 := by decide +kernel

theorem rows22250R_798 : rowsJ2 58 59 21 23 ≤ 127542241869 := by decide +kernel

theorem rows22250R_799 : rowsJ2 58 59 23 24 ≤ 40894209469 := by decide +kernel

theorem rows22250R_800 : rowsJ2 58 59 24 25 ≤ 27275831001 := by decide +kernel

theorem rows22250R_801 : rowsJ2 58 59 25 26 ≤ 18730961516 := by decide +kernel

theorem rows22250R_802 : rowsJ2 58 59 26 27 ≤ 9674007494 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_792
#print axioms SieveCert.rows22250R_802
