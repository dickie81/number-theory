/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3818–3833 of 4715

File 293 of 351: the parts `rows22250R_3818` … `rows22250R_3833` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 99735 in units of a depth-4 test: row 143 columns 63–63, row 143
columns 64–64, row 143 columns 65–65, row 143 columns 66–66, row 143 columns 67–67, row 143 columns 68–68, row 143
columns 69–69, row 143 columns 70–71, row 143 columns 72–74, row 143 columns 75–80, row 143 columns 81–339, row 144
columns 0–42, row 144 columns 43–48, row 144 columns 49–50, row 144 columns 51–51, row 144 columns 52–52), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3818 : rowsJ2 143 144 63 64 ≤ 10412026297919 := by decide +kernel

theorem rows22250R_3819 : rowsJ2 143 144 64 65 ≤ 9243198578068 := by decide +kernel

theorem rows22250R_3820 : rowsJ2 143 144 65 66 ≤ 8151075025817 := by decide +kernel

theorem rows22250R_3821 : rowsJ2 143 144 66 67 ≤ 7133843882052 := by decide +kernel

theorem rows22250R_3822 : rowsJ2 143 144 67 68 ≤ 6189826301808 := by decide +kernel

theorem rows22250R_3823 : rowsJ2 143 144 68 69 ≤ 5317471017514 := by decide +kernel

theorem rows22250R_3824 : rowsJ2 143 144 69 70 ≤ 4515349505055 := by decide +kernel

theorem rows22250R_3825 : rowsJ2 143 144 70 72 ≤ 6898833323285 := by decide +kernel

theorem rows22250R_3826 : rowsJ2 143 144 72 75 ≤ 6018879498053 := by decide +kernel

theorem rows22250R_3827 : rowsJ2 143 144 75 81 ≤ 2806556199363 := by decide +kernel

theorem rows22250R_3828 : rowsJ2 143 144 81 340 ≤ 1282020465869389 := by decide +kernel

theorem rows22250R_3829 : rowsJ2 144 145 0 43 ≤ 1312013116401 := by decide +kernel

theorem rows22250R_3830 : rowsJ2 144 145 43 49 ≤ 9417978935597 := by decide +kernel

theorem rows22250R_3831 : rowsJ2 144 145 49 51 ≤ 7703202988528 := by decide +kernel

theorem rows22250R_3832 : rowsJ2 144 145 51 52 ≤ 4968383093842 := by decide +kernel

theorem rows22250R_3833 : rowsJ2 144 145 52 53 ≤ 5781568818111 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3818
#print axioms SieveCert.rows22250R_3833
