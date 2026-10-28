/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3836–3849 of 5066

File 304 of 387: the parts `rows22240R_3836` … `rows22240R_3849` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 95933 in units of a depth-4 test: row 133 columns 68–68, row 133
columns 69–69, row 133 columns 70–70, row 133 columns 71–71, row 133 columns 72–72, row 133 columns 73–73, row 133
columns 74–74, row 133 columns 75–75, row 133 columns 76–77, row 133 columns 78–79, row 133 columns 80–82, row 133
columns 83–85, row 133 columns 86–339, row 134 columns 0–23), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_3836 : rowsJ2 133 134 68 69 ≤ 8898769937850 := by decide +kernel

theorem rows22240R_3837 : rowsJ2 133 134 69 70 ≤ 7970435121898 := by decide +kernel

theorem rows22240R_3838 : rowsJ2 133 134 70 71 ≤ 7111138257319 := by decide +kernel

theorem rows22240R_3839 : rowsJ2 133 134 71 72 ≤ 6297215721227 := by decide +kernel

theorem rows22240R_3840 : rowsJ2 133 134 72 73 ≤ 5549219722144 := by decide +kernel

theorem rows22240R_3841 : rowsJ2 133 134 73 74 ≤ 4843381229149 := by decide +kernel

theorem rows22240R_3842 : rowsJ2 133 134 74 75 ≤ 4200704956105 := by decide +kernel

theorem rows22240R_3843 : rowsJ2 133 134 75 76 ≤ 3597281343804 := by decide +kernel

theorem rows22240R_3844 : rowsJ2 133 134 76 78 ≤ 5603086449378 := by decide +kernel

theorem rows22240R_3845 : rowsJ2 133 134 78 80 ≤ 3788838964697 := by decide +kernel

theorem rows22240R_3846 : rowsJ2 133 134 80 83 ≤ 5887923298150 := by decide +kernel

theorem rows22240R_3847 : rowsJ2 133 134 83 86 ≤ 14161035525617 := by decide +kernel

theorem rows22240R_3848 : rowsJ2 133 134 86 340 ≤ 623315170680977 := by decide +kernel

theorem rows22240R_3849 : rowsJ2 134 135 0 24 ≤ 3581508822425 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3836
#print axioms SieveCert.rows22240R_3849
