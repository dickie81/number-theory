/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3681–3694 of 5066

File 293 of 387: the parts `rows22240R_3681` … `rows22240R_3694` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 96141 in units of a depth-4 test: row 128 columns 64–64, row 128
columns 65–65, row 128 columns 66–66, row 128 columns 67–67, row 128 columns 68–68, row 128 columns 69–69, row 128
columns 70–70, row 128 columns 71–71, row 128 columns 72–72, row 128 columns 73–73, row 128 columns 74–74, row 128
columns 75–75, row 128 columns 76–76, row 128 columns 77–78), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_3681 : rowsJ2 128 129 64 65 ≤ 6370079148273 := by decide +kernel

theorem rows22240R_3682 : rowsJ2 128 129 65 66 ≤ 6768191006190 := by decide +kernel

theorem rows22240R_3683 : rowsJ2 128 129 66 67 ≤ 7117179999636 := by decide +kernel

theorem rows22240R_3684 : rowsJ2 128 129 67 68 ≤ 7394095473382 := by decide +kernel

theorem rows22240R_3685 : rowsJ2 128 129 68 69 ≤ 7620268414106 := by decide +kernel

theorem rows22240R_3686 : rowsJ2 128 129 69 70 ≤ 7772287410819 := by decide +kernel

theorem rows22240R_3687 : rowsJ2 128 129 70 71 ≤ 6916975384007 := by decide +kernel

theorem rows22240R_3688 : rowsJ2 128 129 71 72 ≤ 6106585173265 := by decide +kernel

theorem rows22240R_3689 : rowsJ2 128 129 72 73 ≤ 5362315990265 := by decide +kernel

theorem rows22240R_3690 : rowsJ2 128 129 73 74 ≤ 4659737366620 := by decide +kernel

theorem rows22240R_3691 : rowsJ2 128 129 74 75 ≤ 4020502676454 := by decide +kernel

theorem rows22240R_3692 : rowsJ2 128 129 75 76 ≤ 3420038455389 := by decide +kernel

theorem rows22240R_3693 : rowsJ2 128 129 76 77 ≤ 2880457288568 := by decide +kernel

theorem rows22240R_3694 : rowsJ2 128 129 77 79 ≤ 4309311894886 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3681
#print axioms SieveCert.rows22240R_3694
