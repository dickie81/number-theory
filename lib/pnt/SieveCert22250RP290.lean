/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3778–3791 of 4715

File 290 of 351: the parts `rows22250R_3778` … `rows22250R_3791` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 97483 in units of a depth-4 test: row 141 columns 81–339, row 142
columns 0–27, row 142 columns 28–48, row 142 columns 49–50, row 142 columns 51–52, row 142 columns 53–53, row 142
columns 54–54, row 142 columns 55–55, row 142 columns 56–56, row 142 columns 57–57, row 142 columns 58–58, row 142
columns 59–59, row 142 columns 60–60, row 142 columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3778 : rowsJ2 141 142 81 340 ≤ 1080020640696416 := by decide +kernel

theorem rows22250R_3779 : rowsJ2 142 143 0 28 ≤ 2018598746354 := by decide +kernel

theorem rows22250R_3780 : rowsJ2 142 143 28 49 ≤ 6695488929560 := by decide +kernel

theorem rows22250R_3781 : rowsJ2 142 143 49 51 ≤ 6132499088632 := by decide +kernel

theorem rows22250R_3782 : rowsJ2 142 143 51 53 ≤ 8875597802404 := by decide +kernel

theorem rows22250R_3783 : rowsJ2 142 143 53 54 ≤ 5594344203864 := by decide +kernel

theorem rows22250R_3784 : rowsJ2 142 143 54 55 ≤ 6429229758617 := by decide +kernel

theorem rows22250R_3785 : rowsJ2 142 143 55 56 ≤ 7309577010149 := by decide +kernel

theorem rows22250R_3786 : rowsJ2 142 143 56 57 ≤ 8233625060651 := by decide +kernel

theorem rows22250R_3787 : rowsJ2 142 143 57 58 ≤ 9199755878540 := by decide +kernel

theorem rows22250R_3788 : rowsJ2 142 143 58 59 ≤ 10206486886353 := by decide +kernel

theorem rows22250R_3789 : rowsJ2 142 143 59 60 ≤ 11252464208103 := by decide +kernel

theorem rows22250R_3790 : rowsJ2 142 143 60 61 ≤ 12316031891359 := by decide +kernel

theorem rows22250R_3791 : rowsJ2 142 143 61 62 ≤ 13335520549357 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3778
#print axioms SieveCert.rows22250R_3791
