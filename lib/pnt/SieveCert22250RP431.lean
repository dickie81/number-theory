/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5265–5278 of 5796

File 431 of 465: the parts `rows22250R_5265` … `rows22250R_5278` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 93957 tests: row 173 columns 52–52, row 173 columns 53–53, row 173 columns
54–54, row 173 columns 55–55, row 173 columns 56–56, row 173 columns 57–57, row 173 columns 58–58, row 173 columns
59–59, row 173 columns 60–60, row 173 columns 61–61, row 173 columns 62–62, row 173 columns 63–64, row 173 columns
65–129, row 173 columns 130–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_5265 : rowsJ2 173 174 52 53 ≤ 15888473061484 := by decide +kernel

theorem rows22250R_5266 : rowsJ2 173 174 53 54 ≤ 17245268230083 := by decide +kernel

theorem rows22250R_5267 : rowsJ2 173 174 54 55 ≤ 17079126832932 := by decide +kernel

theorem rows22250R_5268 : rowsJ2 173 174 55 56 ≤ 15433644905208 := by decide +kernel

theorem rows22250R_5269 : rowsJ2 173 174 56 57 ≤ 13884543713930 := by decide +kernel

theorem rows22250R_5270 : rowsJ2 173 174 57 58 ≤ 12428966350642 := by decide +kernel

theorem rows22250R_5271 : rowsJ2 173 174 58 59 ≤ 11064256356798 := by decide +kernel

theorem rows22250R_5272 : rowsJ2 173 174 59 60 ≤ 9787947508748 := by decide +kernel

theorem rows22250R_5273 : rowsJ2 173 174 60 61 ≤ 8597754535499 := by decide +kernel

theorem rows22250R_5274 : rowsJ2 173 174 61 62 ≤ 7491564699327 := by decide +kernel

theorem rows22250R_5275 : rowsJ2 173 174 62 63 ≤ 6467430177073 := by decide +kernel

theorem rows22250R_5276 : rowsJ2 173 174 63 65 ≤ 10181881003293 := by decide +kernel

theorem rows22250R_5277 : rowsJ2 173 174 65 130 ≤ 871569331923288 := by decide +kernel

theorem rows22250R_5278 : rowsJ2 173 174 130 360 ≤ 1666191192921090 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5265
#print axioms SieveCert.rows22250R_5278
