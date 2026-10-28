/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1104–1110 of 5066

File 108 of 387: the parts `rows22240R_1104` … `rows22240R_1110` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 96679 in units of a depth-4 test: row 64 columns 55–55, row 64 columns
56–56, row 64 columns 57–57, row 64 columns 58–58, row 64 columns 59–59, row 64 columns 60–60, row 64 columns
61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1104 : rowsJ2 64 65 55 56 ≤ 8722779862582 := by decide +kernel

theorem rows22240R_1105 : rowsJ2 64 65 56 57 ≤ 9718460535964 := by decide +kernel

theorem rows22240R_1106 : rowsJ2 64 65 57 58 ≤ 10484306543052 := by decide +kernel

theorem rows22240R_1107 : rowsJ2 64 65 58 59 ≤ 11066818910129 := by decide +kernel

theorem rows22240R_1108 : rowsJ2 64 65 59 60 ≤ 11621263015743 := by decide +kernel

theorem rows22240R_1109 : rowsJ2 64 65 60 61 ≤ 11107903420653 := by decide +kernel

theorem rows22240R_1110 : rowsJ2 64 65 61 62 ≤ 10600706162150 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1104
#print axioms SieveCert.rows22240R_1110
