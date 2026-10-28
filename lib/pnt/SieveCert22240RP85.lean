/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 849–857 of 5066

File 85 of 387: the parts `rows22240R_849` … `rows22240R_857` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 98003 in units of a depth-4 test: row 58 columns 49–49, row 58 columns
50–50, row 58 columns 51–51, row 58 columns 52–52, row 58 columns 53–53, row 58 columns 54–54, row 58 columns 55–55,
row 58 columns 56–56, row 58 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_849 : rowsJ2 58 59 49 50 ≤ 2557898854349 := by decide +kernel

theorem rows22240R_850 : rowsJ2 58 59 50 51 ≤ 3490233695966 := by decide +kernel

theorem rows22240R_851 : rowsJ2 58 59 51 52 ≤ 4592273283164 := by decide +kernel

theorem rows22240R_852 : rowsJ2 58 59 52 53 ≤ 6002303549696 := by decide +kernel

theorem rows22240R_853 : rowsJ2 58 59 53 54 ≤ 7429450240526 := by decide +kernel

theorem rows22240R_854 : rowsJ2 58 59 54 55 ≤ 8869270805313 := by decide +kernel

theorem rows22240R_855 : rowsJ2 58 59 55 56 ≤ 10276384556548 := by decide +kernel

theorem rows22240R_856 : rowsJ2 58 59 56 57 ≤ 11796938951649 := by decide +kernel

theorem rows22240R_857 : rowsJ2 58 59 57 58 ≤ 13090643916155 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_849
#print axioms SieveCert.rows22240R_857
