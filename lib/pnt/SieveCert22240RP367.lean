/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4727–4741 of 5066

File 367 of 387: the parts `rows22240R_4727` … `rows22240R_4741` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 95932 in units of a depth-4 test: row 170 columns 46–46, row 170
columns 47–47, row 170 columns 48–48, row 170 columns 49–49, row 170 columns 50–50, row 170 columns 51–51, row 170
columns 52–52, row 170 columns 53–53, row 170 columns 54–54, row 170 columns 55–56, row 170 columns 57–339, row 171
columns 0–36, row 171 columns 37–39, row 171 columns 40–41, row 171 columns 42–42), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4727 : rowsJ2 170 171 46 47 ≤ 19398756080869 := by decide +kernel

theorem rows22240R_4728 : rowsJ2 170 171 47 48 ≤ 21183308535459 := by decide +kernel

theorem rows22240R_4729 : rowsJ2 170 171 48 49 ≤ 23025375315697 := by decide +kernel

theorem rows22240R_4730 : rowsJ2 170 171 49 50 ≤ 20740382179843 := by decide +kernel

theorem rows22240R_4731 : rowsJ2 170 171 50 51 ≤ 18595864086577 := by decide +kernel

theorem rows22240R_4732 : rowsJ2 170 171 51 52 ≤ 16587034799933 := by decide +kernel

theorem rows22240R_4733 : rowsJ2 170 171 52 53 ≤ 14709453691724 := by decide +kernel

theorem rows22240R_4734 : rowsJ2 170 171 53 54 ≤ 12959013219815 := by decide +kernel

theorem rows22240R_4735 : rowsJ2 170 171 54 55 ≤ 11331951141802 := by decide +kernel

theorem rows22240R_4736 : rowsJ2 170 171 55 57 ≤ 18259252767682 := by decide +kernel

theorem rows22240R_4737 : rowsJ2 170 171 57 340 ≤ 2683449120908470 := by decide +kernel

theorem rows22240R_4738 : rowsJ2 171 172 0 37 ≤ 12942915900729 := by decide +kernel

theorem rows22240R_4739 : rowsJ2 171 172 37 40 ≤ 24617866740993 := by decide +kernel

theorem rows22240R_4740 : rowsJ2 171 172 40 42 ≤ 23253007323168 := by decide +kernel

theorem rows22240R_4741 : rowsJ2 171 172 42 43 ≤ 13896286875923 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4727
#print axioms SieveCert.rows22240R_4741
