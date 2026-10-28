/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4586–4600 of 5066

File 358 of 387: the parts `rows22240R_4586` … `rows22240R_4600` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 99072 in units of a depth-4 test: row 163 columns 46–46, row 163
columns 47–47, row 163 columns 48–48, row 163 columns 49–49, row 163 columns 50–50, row 163 columns 51–51, row 163
columns 52–52, row 163 columns 53–53, row 163 columns 54–54, row 163 columns 55–55, row 163 columns 56–56, row 163
columns 57–57, row 163 columns 58–58, row 163 columns 59–60, row 163 columns 61–62), each a sum of refined costs
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

theorem rows22240R_4586 : rowsJ2 163 164 46 47 ≤ 11833802885067 := by decide +kernel

theorem rows22240R_4587 : rowsJ2 163 164 47 48 ≤ 13205921598984 := by decide +kernel

theorem rows22240R_4588 : rowsJ2 163 164 48 49 ≤ 14633978620136 := by decide +kernel

theorem rows22240R_4589 : rowsJ2 163 164 49 50 ≤ 16116221155579 := by decide +kernel

theorem rows22240R_4590 : rowsJ2 163 164 50 51 ≤ 17651070210342 := by decide +kernel

theorem rows22240R_4591 : rowsJ2 163 164 51 52 ≤ 19237116767474 := by decide +kernel

theorem rows22240R_4592 : rowsJ2 163 164 52 53 ≤ 19042208550981 := by decide +kernel

theorem rows22240R_4593 : rowsJ2 163 164 53 54 ≤ 17119891573188 := by decide +kernel

theorem rows22240R_4594 : rowsJ2 163 164 54 55 ≤ 15315845240036 := by decide +kernel

theorem rows22240R_4595 : rowsJ2 163 164 55 56 ≤ 13626385423324 := by decide +kernel

theorem rows22240R_4596 : rowsJ2 163 164 56 57 ≤ 12048103599586 := by decide +kernel

theorem rows22240R_4597 : rowsJ2 163 164 57 58 ≤ 10577841765669 := by decide +kernel

theorem rows22240R_4598 : rowsJ2 163 164 58 59 ≤ 9212679168532 := by decide +kernel

theorem rows22240R_4599 : rowsJ2 163 164 59 61 ≤ 14736972315752 := by decide +kernel

theorem rows22240R_4600 : rowsJ2 163 164 61 63 ≤ 10474157491761 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4586
#print axioms SieveCert.rows22240R_4600
