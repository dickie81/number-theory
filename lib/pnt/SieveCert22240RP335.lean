/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4251–4265 of 5066

File 335 of 387: the parts `rows22240R_4251` … `rows22240R_4265` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 93639 in units of a depth-4 test: row 148 columns 65–65, row 148
columns 66–66, row 148 columns 67–67, row 148 columns 68–69, row 148 columns 70–71, row 148 columns 72–75, row 148
columns 76–339, row 149 columns 0–42, row 149 columns 43–46, row 149 columns 47–48, row 149 columns 49–50, row 149
columns 51–51, row 149 columns 52–52, row 149 columns 53–53, row 149 columns 54–54), each a sum of refined costs
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

theorem rows22240R_4251 : rowsJ2 148 149 65 66 ≤ 7600578413475 := by decide +kernel

theorem rows22240R_4252 : rowsJ2 148 149 66 67 ≤ 6594243753688 := by decide +kernel

theorem rows22240R_4253 : rowsJ2 148 149 67 68 ≤ 5664464571559 := by decide +kernel

theorem rows22240R_4254 : rowsJ2 148 149 68 70 ≤ 8838156710373 := by decide +kernel

theorem rows22240R_4255 : rowsJ2 148 149 70 72 ≤ 6001158161942 := by decide +kernel

theorem rows22240R_4256 : rowsJ2 148 149 72 76 ≤ 5734413510084 := by decide +kernel

theorem rows22240R_4257 : rowsJ2 148 149 76 340 ≤ 1666332715948608 := by decide +kernel

theorem rows22240R_4258 : rowsJ2 149 150 0 43 ≤ 2188701904552 := by decide +kernel

theorem rows22240R_4259 : rowsJ2 149 150 43 47 ≤ 8707231597084 := by decide +kernel

theorem rows22240R_4260 : rowsJ2 149 150 47 49 ≤ 8317747030310 := by decide +kernel

theorem rows22240R_4261 : rowsJ2 149 150 49 51 ≤ 11599426492144 := by decide +kernel

theorem rows22240R_4262 : rowsJ2 149 150 51 52 ≤ 7165235567650 := by decide +kernel

theorem rows22240R_4263 : rowsJ2 149 150 52 53 ≤ 8143135439752 := by decide +kernel

theorem rows22240R_4264 : rowsJ2 149 150 53 54 ≤ 9169219782288 := by decide +kernel

theorem rows22240R_4265 : rowsJ2 149 150 54 55 ≤ 10241682265809 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4251
#print axioms SieveCert.rows22240R_4265
