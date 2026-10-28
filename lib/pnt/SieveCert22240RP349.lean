/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4452–4465 of 5066

File 349 of 387: the parts `rows22240R_4452` … `rows22240R_4465` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 99068 in units of a depth-4 test: row 157 columns 42–44, row 157
columns 45–46, row 157 columns 47–47, row 157 columns 48–48, row 157 columns 49–49, row 157 columns 50–50, row 157
columns 51–51, row 157 columns 52–52, row 157 columns 53–53, row 157 columns 54–54, row 157 columns 55–55, row 157
columns 56–56, row 157 columns 57–57, row 157 columns 58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_4452 : rowsJ2 157 158 42 45 ≤ 13172623971038 := by decide +kernel

theorem rows22240R_4453 : rowsJ2 157 158 45 47 ≤ 13394031327182 := by decide +kernel

theorem rows22240R_4454 : rowsJ2 157 158 47 48 ≤ 8266646938952 := by decide +kernel

theorem rows22240R_4455 : rowsJ2 157 158 48 49 ≤ 9389480839911 := by decide +kernel

theorem rows22240R_4456 : rowsJ2 157 158 49 50 ≤ 10566816265683 := by decide +kernel

theorem rows22240R_4457 : rowsJ2 157 158 50 51 ≤ 11796669682552 := by decide +kernel

theorem rows22240R_4458 : rowsJ2 157 158 51 52 ≤ 13077217034070 := by decide +kernel

theorem rows22240R_4459 : rowsJ2 157 158 52 53 ≤ 14406792654151 := by decide +kernel

theorem rows22240R_4460 : rowsJ2 157 158 53 54 ≤ 15783899223600 := by decide +kernel

theorem rows22240R_4461 : rowsJ2 157 158 54 55 ≤ 17207188737600 := by decide +kernel

theorem rows22240R_4462 : rowsJ2 157 158 55 56 ≤ 17038062571825 := by decide +kernel

theorem rows22240R_4463 : rowsJ2 157 158 56 57 ≤ 15323008038859 := by decide +kernel

theorem rows22240R_4464 : rowsJ2 157 158 57 58 ≤ 13712368060388 := by decide +kernel

theorem rows22240R_4465 : rowsJ2 157 158 58 59 ≤ 12203076703812 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4452
#print axioms SieveCert.rows22240R_4465
