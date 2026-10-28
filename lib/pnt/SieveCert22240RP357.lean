/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4571–4585 of 5066

File 357 of 387: the parts `rows22240R_4571` … `rows22240R_4585` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 98792 in units of a depth-4 test: row 162 columns 52–52, row 162
columns 53–53, row 162 columns 54–54, row 162 columns 55–55, row 162 columns 56–56, row 162 columns 57–57, row 162
columns 58–58, row 162 columns 59–59, row 162 columns 60–61, row 162 columns 62–64, row 162 columns 65–339, row 163
columns 0–39, row 163 columns 40–42, row 163 columns 43–44, row 163 columns 45–45), each a sum of refined costs
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

theorem rows22240R_4571 : rowsJ2 162 163 52 53 ≤ 19684621523447 := by decide +kernel

theorem rows22240R_4572 : rowsJ2 162 163 53 54 ≤ 17739881579318 := by decide +kernel

theorem rows22240R_4573 : rowsJ2 162 163 54 55 ≤ 15912821404934 := by decide +kernel

theorem rows22240R_4574 : rowsJ2 162 163 55 56 ≤ 14199729400932 := by decide +kernel

theorem rows22240R_4575 : rowsJ2 162 163 56 57 ≤ 12597164784124 := by decide +kernel

theorem rows22240R_4576 : rowsJ2 162 163 57 58 ≤ 11101946029353 := by decide +kernel

theorem rows22240R_4577 : rowsJ2 162 163 58 59 ≤ 9711127137335 := by decide +kernel

theorem rows22240R_4578 : rowsJ2 162 163 59 60 ≤ 8421985542435 := by decide +kernel

theorem rows22240R_4579 : rowsJ2 162 163 60 62 ≤ 13370875897982 := by decide +kernel

theorem rows22240R_4580 : rowsJ2 162 163 62 65 ≤ 12796175792107 := by decide +kernel

theorem rows22240R_4581 : rowsJ2 162 163 65 340 ≤ 2593401191614631 := by decide +kernel

theorem rows22240R_4582 : rowsJ2 163 164 0 40 ≤ 11956546458567 := by decide +kernel

theorem rows22240R_4583 : rowsJ2 163 164 40 43 ≤ 17744980746339 := by decide +kernel

theorem rows22240R_4584 : rowsJ2 163 164 43 45 ≤ 17339776666600 := by decide +kernel

theorem rows22240R_4585 : rowsJ2 163 164 45 46 ≤ 10519590205705 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4571
#print axioms SieveCert.rows22240R_4585
