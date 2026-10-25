/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5457–5472 of 5796

File 444 of 465: the parts `rows22250R_5457` … `rows22250R_5472` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94496 tests: row 182 columns 49–49, row 182 columns 50–50, row 182 columns
51–51, row 182 columns 52–52, row 182 columns 53–53, row 182 columns 54–54, row 182 columns 55–55, row 182 columns
56–56, row 182 columns 57–120, row 182 columns 121–359, row 183 columns 0–37, row 183 columns 38–39, row 183 columns
40–41, row 183 columns 42–42, row 183 columns 43–43, row 183 columns 44–44), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5457 : rowsJ2 182 183 49 50 ≤ 21271512811195 := by decide +kernel

theorem rows22250R_5458 : rowsJ2 182 183 50 51 ≤ 19252910134023 := by decide +kernel

theorem rows22250R_5459 : rowsJ2 182 183 51 52 ≤ 17352911665041 := by decide +kernel

theorem rows22250R_5460 : rowsJ2 182 183 52 53 ≤ 15567626289253 := by decide +kernel

theorem rows22250R_5461 : rowsJ2 182 183 53 54 ≤ 13893443857210 := by decide +kernel

theorem rows22250R_5462 : rowsJ2 182 183 54 55 ≤ 12327019320645 := by decide +kernel

theorem rows22250R_5463 : rowsJ2 182 183 55 56 ≤ 10865258372713 := by decide +kernel

theorem rows22250R_5464 : rowsJ2 182 183 56 57 ≤ 9505304467853 := by decide +kernel

theorem rows22250R_5465 : rowsJ2 182 183 57 121 ≤ 973941031249740 := by decide +kernel

theorem rows22250R_5466 : rowsJ2 182 183 121 360 ≤ 1673733130916315 := by decide +kernel

theorem rows22250R_5467 : rowsJ2 183 184 0 38 ≤ 12343616125291 := by decide +kernel

theorem rows22250R_5468 : rowsJ2 183 184 38 40 ≤ 14340742086976 := by decide +kernel

theorem rows22250R_5469 : rowsJ2 183 184 40 42 ≤ 19776438825167 := by decide +kernel

theorem rows22250R_5470 : rowsJ2 183 184 42 43 ≤ 11826553160197 := by decide +kernel

theorem rows22250R_5471 : rowsJ2 183 184 43 44 ≤ 13196408437594 := by decide +kernel

theorem rows22250R_5472 : rowsJ2 183 184 44 45 ≤ 14621895125388 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5457
#print axioms SieveCert.rows22250R_5472
