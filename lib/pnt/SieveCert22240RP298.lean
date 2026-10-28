/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3752–3767 of 5066

File 298 of 387: the parts `rows22240R_3752` … `rows22240R_3767` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 94744 in units of a depth-4 test: row 130 columns 75–75, row 130
columns 76–76, row 130 columns 77–78, row 130 columns 79–80, row 130 columns 81–83, row 130 columns 84–86, row 130
columns 87–96, row 130 columns 97–339, row 131 columns 0–24, row 131 columns 25–28, row 131 columns 29–37, row 131
columns 38–53, row 131 columns 54–56, row 131 columns 57–57, row 131 columns 58–58, row 131 columns 59–59), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3752 : rowsJ2 130 131 75 76 ≤ 3610036771503 := by decide +kernel

theorem rows22240R_3753 : rowsJ2 130 131 76 77 ≤ 3069105863617 := by decide +kernel

theorem rows22240R_3754 : rowsJ2 130 131 77 79 ≤ 4683129538477 := by decide +kernel

theorem rows22240R_3755 : rowsJ2 130 131 79 81 ≤ 3058165208809 := by decide +kernel

theorem rows22240R_3756 : rowsJ2 130 131 81 84 ≤ 7293169024750 := by decide +kernel

theorem rows22240R_3757 : rowsJ2 130 131 84 87 ≤ 15472681953648 := by decide +kernel

theorem rows22240R_3758 : rowsJ2 130 131 87 97 ≤ 641889312164778 := by decide +kernel

theorem rows22240R_3759 : rowsJ2 130 131 97 340 ≤ 164883981358033 := by decide +kernel

theorem rows22240R_3760 : rowsJ2 131 132 0 25 ≤ 4662333821957 := by decide +kernel

theorem rows22240R_3761 : rowsJ2 131 132 25 29 ≤ 15047311363978 := by decide +kernel

theorem rows22240R_3762 : rowsJ2 131 132 29 38 ≤ 8266702795145 := by decide +kernel

theorem rows22240R_3763 : rowsJ2 131 132 38 54 ≤ 3756402397075 := by decide +kernel

theorem rows22240R_3764 : rowsJ2 131 132 54 57 ≤ 6925056452164 := by decide +kernel

theorem rows22240R_3765 : rowsJ2 131 132 57 58 ≤ 3397755704061 := by decide +kernel

theorem rows22240R_3766 : rowsJ2 131 132 58 59 ≤ 4017636456994 := by decide +kernel

theorem rows22240R_3767 : rowsJ2 131 132 59 60 ≤ 4679750567970 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3752
#print axioms SieveCert.rows22240R_3767
