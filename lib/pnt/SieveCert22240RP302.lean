/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3808–3822 of 5066

File 302 of 387: the parts `rows22240R_3808` … `rows22240R_3822` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 95356 in units of a depth-4 test: row 132 columns 70–70, row 132
columns 71–71, row 132 columns 72–72, row 132 columns 73–73, row 132 columns 74–74, row 132 columns 75–75, row 132
columns 76–76, row 132 columns 77–78, row 132 columns 79–80, row 132 columns 81–83, row 132 columns 84–86, row 132
columns 87–339, row 133 columns 0–23, row 133 columns 24–28, row 133 columns 29–48), each a sum of refined costs
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

theorem rows22240R_3808 : rowsJ2 132 133 70 71 ≤ 7155598568160 := by decide +kernel

theorem rows22240R_3809 : rowsJ2 132 133 71 72 ≤ 6342274363655 := by decide +kernel

theorem rows22240R_3810 : rowsJ2 132 133 72 73 ≤ 5594915876351 := by decide +kernel

theorem rows22240R_3811 : rowsJ2 132 133 73 74 ≤ 4889623506561 := by decide +kernel

theorem rows22240R_3812 : rowsJ2 132 133 74 75 ≤ 4247534256955 := by decide +kernel

theorem rows22240R_3813 : rowsJ2 132 133 75 76 ≤ 3644608273242 := by decide +kernel

theorem rows22240R_3814 : rowsJ2 132 133 76 77 ≤ 3102431778883 := by decide +kernel

theorem rows22240R_3815 : rowsJ2 132 133 77 79 ≤ 4746578095958 := by decide +kernel

theorem rows22240R_3816 : rowsJ2 132 133 79 81 ≤ 3117765092611 := by decide +kernel

theorem rows22240R_3817 : rowsJ2 132 133 81 84 ≤ 7997731997461 := by decide +kernel

theorem rows22240R_3818 : rowsJ2 132 133 84 87 ≤ 17268300556645 := by decide +kernel

theorem rows22240R_3819 : rowsJ2 132 133 87 340 ≤ 704538513414617 := by decide +kernel

theorem rows22240R_3820 : rowsJ2 133 134 0 24 ≤ 3042148595910 := by decide +kernel

theorem rows22240R_3821 : rowsJ2 133 134 24 29 ≤ 14628741829953 := by decide +kernel

theorem rows22240R_3822 : rowsJ2 133 134 29 49 ≤ 4157259656153 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3808
#print axioms SieveCert.rows22240R_3822
