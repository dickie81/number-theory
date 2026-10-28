/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3850–3863 of 5066

File 305 of 387: the parts `rows22240R_3850` … `rows22240R_3863` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 98359 in units of a depth-4 test: row 134 columns 24–29, row 134
columns 30–50, row 134 columns 51–53, row 134 columns 54–55, row 134 columns 56–56, row 134 columns 57–57, row 134
columns 58–58, row 134 columns 59–59, row 134 columns 60–60, row 134 columns 61–61, row 134 columns 62–62, row 134
columns 63–63, row 134 columns 64–64, row 134 columns 65–65), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_3850 : rowsJ2 134 135 24 30 ≤ 14114970165832 := by decide +kernel

theorem rows22240R_3851 : rowsJ2 134 135 30 51 ≤ 3248034164175 := by decide +kernel

theorem rows22240R_3852 : rowsJ2 134 135 51 54 ≤ 5070958885524 := by decide +kernel

theorem rows22240R_3853 : rowsJ2 134 135 54 56 ≤ 5934494815551 := by decide +kernel

theorem rows22240R_3854 : rowsJ2 134 135 56 57 ≤ 3880874985193 := by decide +kernel

theorem rows22240R_3855 : rowsJ2 134 135 57 58 ≤ 4550560881179 := by decide +kernel

theorem rows22240R_3856 : rowsJ2 134 135 58 59 ≤ 5263302685014 := by decide +kernel

theorem rows22240R_3857 : rowsJ2 134 135 59 60 ≤ 6017328689843 := by decide +kernel

theorem rows22240R_3858 : rowsJ2 134 135 60 61 ≤ 6810955384979 := by decide +kernel

theorem rows22240R_3859 : rowsJ2 134 135 61 62 ≤ 7621913068849 := by decide +kernel

theorem rows22240R_3860 : rowsJ2 134 135 62 63 ≤ 8387339339646 := by decide +kernel

theorem rows22240R_3861 : rowsJ2 134 135 63 64 ≤ 9086071251810 := by decide +kernel

theorem rows22240R_3862 : rowsJ2 134 135 64 65 ≤ 9738682520532 := by decide +kernel

theorem rows22240R_3863 : rowsJ2 134 135 65 66 ≤ 10323625089785 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3850
#print axioms SieveCert.rows22240R_3863
