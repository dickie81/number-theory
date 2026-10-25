/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5279–5292 of 5796

File 432 of 465: the parts `rows22250R_5279` … `rows22250R_5292` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98476 tests: row 174 columns 0–40, row 174 columns 41–42, row 174 columns
43–44, row 174 columns 45–45, row 174 columns 46–46, row 174 columns 47–47, row 174 columns 48–48, row 174 columns
49–49, row 174 columns 50–50, row 174 columns 51–51, row 174 columns 52–52, row 174 columns 53–53, row 174 columns
54–54, row 174 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5279 : rowsJ2 174 175 0 41 ≤ 10633475492450 := by decide +kernel

theorem rows22250R_5280 : rowsJ2 174 175 41 43 ≤ 9904115812327 := by decide +kernel

theorem rows22250R_5281 : rowsJ2 174 175 43 45 ≤ 13574097485784 := by decide +kernel

theorem rows22250R_5282 : rowsJ2 174 175 45 46 ≤ 8304410444645 := by decide +kernel

theorem rows22250R_5283 : rowsJ2 174 175 46 47 ≤ 9386540948847 := by decide +kernel

theorem rows22250R_5284 : rowsJ2 174 175 47 48 ≤ 10519004889182 := by decide +kernel

theorem rows22250R_5285 : rowsJ2 174 175 48 49 ≤ 11699963015608 := by decide +kernel

theorem rows22250R_5286 : rowsJ2 174 175 49 50 ≤ 12927754170290 := by decide +kernel

theorem rows22250R_5287 : rowsJ2 174 175 50 51 ≤ 14200886493628 := by decide +kernel

theorem rows22250R_5288 : rowsJ2 174 175 51 52 ≤ 15518029560850 := by decide +kernel

theorem rows22250R_5289 : rowsJ2 174 175 52 53 ≤ 16878007396732 := by decide +kernel

theorem rows22250R_5290 : rowsJ2 174 175 53 54 ≤ 18279792322966 := by decide +kernel

theorem rows22250R_5291 : rowsJ2 174 175 54 55 ≤ 16552801004762 := by decide +kernel

theorem rows22250R_5292 : rowsJ2 174 175 55 56 ≤ 14925731253637 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5279
#print axioms SieveCert.rows22250R_5292
