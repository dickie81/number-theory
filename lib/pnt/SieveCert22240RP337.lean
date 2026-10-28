/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4279–4293 of 5066

File 337 of 387: the parts `rows22240R_4279` … `rows22240R_4293` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 93710 in units of a depth-4 test: row 149 columns 68–69, row 149
columns 70–72, row 149 columns 73–78, row 149 columns 79–339, row 150 columns 0–42, row 150 columns 43–46, row 150
columns 47–48, row 150 columns 49–49, row 150 columns 50–50, row 150 columns 51–51, row 150 columns 52–52, row 150
columns 53–53, row 150 columns 54–54, row 150 columns 55–55, row 150 columns 56–56), each a sum of refined costs
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

theorem rows22240R_4279 : rowsJ2 149 150 68 70 ≤ 8190426627446 := by decide +kernel

theorem rows22240R_4280 : rowsJ2 149 150 70 73 ≤ 7329477488792 := by decide +kernel

theorem rows22240R_4281 : rowsJ2 149 150 73 79 ≤ 3740906427322 := by decide +kernel

theorem rows22240R_4282 : rowsJ2 149 150 79 340 ≤ 1787543061855645 := by decide +kernel

theorem rows22240R_4283 : rowsJ2 150 151 0 43 ≤ 2751672595197 := by decide +kernel

theorem rows22240R_4284 : rowsJ2 150 151 43 47 ≤ 10112151842109 := by decide +kernel

theorem rows22240R_4285 : rowsJ2 150 151 47 49 ≤ 9279602998317 := by decide +kernel

theorem rows22240R_4286 : rowsJ2 150 151 49 50 ≤ 5906027646225 := by decide +kernel

theorem rows22240R_4287 : rowsJ2 150 151 50 51 ≤ 6823168892679 := by decide +kernel

theorem rows22240R_4288 : rowsJ2 150 151 51 52 ≤ 7792258090628 := by decide +kernel

theorem rows22240R_4289 : rowsJ2 150 151 52 53 ≤ 8811233912789 := by decide +kernel

theorem rows22240R_4290 : rowsJ2 150 151 53 54 ≤ 9878198575270 := by decide +kernel

theorem rows22240R_4291 : rowsJ2 150 151 54 55 ≤ 10991393396738 := by decide +kernel

theorem rows22240R_4292 : rowsJ2 150 151 55 56 ≤ 12149225053945 := by decide +kernel

theorem rows22240R_4293 : rowsJ2 150 151 56 57 ≤ 13350203591947 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4279
#print axioms SieveCert.rows22240R_4293
