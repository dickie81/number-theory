/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4647–4661 of 5066

File 362 of 387: the parts `rows22240R_4647` … `rows22240R_4661` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 96505 in units of a depth-4 test: row 166 columns 45–45, row 166
columns 46–46, row 166 columns 47–47, row 166 columns 48–48, row 166 columns 49–49, row 166 columns 50–50, row 166
columns 51–51, row 166 columns 52–52, row 166 columns 53–53, row 166 columns 54–54, row 166 columns 55–55, row 166
columns 56–56, row 166 columns 57–58, row 166 columns 59–60, row 166 columns 61–339), each a sum of refined costs
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

theorem rows22240R_4647 : rowsJ2 166 167 45 46 ≤ 13285240857045 := by decide +kernel

theorem rows22240R_4648 : rowsJ2 166 167 46 47 ≤ 14767452242229 := by decide +kernel

theorem rows22240R_4649 : rowsJ2 166 167 47 48 ≤ 16307590443058 := by decide +kernel

theorem rows22240R_4650 : rowsJ2 166 167 48 49 ≤ 17903949384975 := by decide +kernel

theorem rows22240R_4651 : rowsJ2 166 167 49 50 ≤ 19555033158546 := by decide +kernel

theorem rows22240R_4652 : rowsJ2 166 167 50 51 ≤ 21259500341958 := by decide +kernel

theorem rows22240R_4653 : rowsJ2 166 167 51 52 ≤ 19154624636120 := by decide +kernel

theorem rows22240R_4654 : rowsJ2 166 167 52 53 ≤ 17178097641116 := by decide +kernel

theorem rows22240R_4655 : rowsJ2 166 167 53 54 ≤ 15325722901855 := by decide +kernel

theorem rows22240R_4656 : rowsJ2 166 167 54 55 ≤ 13593608030723 := by decide +kernel

theorem rows22240R_4657 : rowsJ2 166 167 55 56 ≤ 11978147110943 := by decide +kernel

theorem rows22240R_4658 : rowsJ2 166 167 56 57 ≤ 10475997940366 := by decide +kernel

theorem rows22240R_4659 : rowsJ2 166 167 57 59 ≤ 16883648746619 := by decide +kernel

theorem rows22240R_4660 : rowsJ2 166 167 59 61 ≤ 12162720521992 := by decide +kernel

theorem rows22240R_4661 : rowsJ2 166 167 61 340 ≤ 2621951371113878 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4647
#print axioms SieveCert.rows22240R_4661
