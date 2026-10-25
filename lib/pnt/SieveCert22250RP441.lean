/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5412–5426 of 5796

File 441 of 465: the parts `rows22250R_5412` … `rows22250R_5426` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99603 tests: row 180 columns 44–44, row 180 columns 45–45, row 180 columns
46–46, row 180 columns 47–47, row 180 columns 48–48, row 180 columns 49–49, row 180 columns 50–50, row 180 columns
51–51, row 180 columns 52–52, row 180 columns 53–53, row 180 columns 54–54, row 180 columns 55–55, row 180 columns
56–56, row 180 columns 57–57, row 180 columns 58–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5412 : rowsJ2 180 181 44 45 ≤ 11795331604031 := by decide +kernel

theorem rows22250R_5413 : rowsJ2 180 181 45 46 ≤ 13114835909306 := by decide +kernel

theorem rows22250R_5414 : rowsJ2 180 181 46 47 ≤ 14486207708513 := by decide +kernel

theorem rows22250R_5415 : rowsJ2 180 181 47 48 ≤ 15907821387674 := by decide +kernel

theorem rows22250R_5416 : rowsJ2 180 181 48 49 ≤ 17378242287844 := by decide +kernel

theorem rows22250R_5417 : rowsJ2 180 181 49 50 ≤ 18896218602836 := by decide +kernel

theorem rows22250R_5418 : rowsJ2 180 181 50 51 ≤ 20460674335344 := by decide +kernel

theorem rows22250R_5419 : rowsJ2 180 181 51 52 ≤ 18521288956135 := by decide +kernel

theorem rows22250R_5420 : rowsJ2 180 181 52 53 ≤ 16695395261314 := by decide +kernel

theorem rows22250R_5421 : rowsJ2 180 181 53 54 ≤ 14979337971621 := by decide +kernel

theorem rows22250R_5422 : rowsJ2 180 181 54 55 ≤ 13369723462084 := by decide +kernel

theorem rows22250R_5423 : rowsJ2 180 181 55 56 ≤ 11863405262422 := by decide +kernel

theorem rows22250R_5424 : rowsJ2 180 181 56 57 ≤ 10457470918145 := by decide +kernel

theorem rows22250R_5425 : rowsJ2 180 181 57 58 ≤ 9149230101770 := by decide +kernel

theorem rows22250R_5426 : rowsJ2 180 181 58 60 ≤ 14752318897249 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5412
#print axioms SieveCert.rows22250R_5426
