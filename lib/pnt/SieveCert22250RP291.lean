/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3792–3804 of 4715

File 291 of 351: the parts `rows22250R_3792` … `rows22250R_3804` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 94267 tests: row 142 columns 62–62, row 142 columns 63–63, row 142 columns
64–64, row 142 columns 65–65, row 142 columns 66–66, row 142 columns 67–67, row 142 columns 68–68, row 142 columns
69–69, row 142 columns 70–71, row 142 columns 72–73, row 142 columns 74–77, row 142 columns 78–339, row 143 columns
0–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3792 : rowsJ2 142 143 62 63 ≤ 12028242851778 := by decide +kernel

theorem rows22250R_3793 : rowsJ2 142 143 63 64 ≤ 10802141834566 := by decide +kernel

theorem rows22250R_3794 : rowsJ2 142 143 64 65 ≤ 9634109505942 := by decide +kernel

theorem rows22250R_3795 : rowsJ2 142 143 65 66 ≤ 8542819013759 := by decide +kernel

theorem rows22250R_3796 : rowsJ2 142 143 66 67 ≤ 7505192900342 := by decide +kernel

theorem rows22250R_3797 : rowsJ2 142 143 67 68 ≤ 6540364758428 := by decide +kernel

theorem rows22250R_3798 : rowsJ2 142 143 68 69 ≤ 5646759645561 := by decide +kernel

theorem rows22250R_3799 : rowsJ2 142 143 69 70 ≤ 4822924299834 := by decide +kernel

theorem rows22250R_3800 : rowsJ2 142 143 70 72 ≤ 7446854818252 := by decide +kernel

theorem rows22250R_3801 : rowsJ2 142 143 72 74 ≤ 4957477585285 := by decide +kernel

theorem rows22250R_3802 : rowsJ2 142 143 74 78 ≤ 4503281099127 := by decide +kernel

theorem rows22250R_3803 : rowsJ2 142 143 78 340 ≤ 1135632214551858 := by decide +kernel

theorem rows22250R_3804 : rowsJ2 143 144 0 42 ≤ 1614479232033 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3792
#print axioms SieveCert.rows22250R_3804
