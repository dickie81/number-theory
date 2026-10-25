/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4565–4582 of 4715

File 342 of 351: the parts `rows22250R_4565` … `rows22250R_4582` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 99367 tests: row 182 columns 33–35, row 182 columns 36–37, row 182 columns
38–38, row 182 columns 39–39, row 182 columns 40–40, row 182 columns 41–41, row 182 columns 42–42, row 182 columns
43–43, row 182 columns 44–44, row 182 columns 45–339, row 183 columns 0–32, row 183 columns 33–34, row 183 columns
35–36, row 183 columns 37–37, row 183 columns 38–38, row 183 columns 39–39, row 183 columns 40–40, row 183 columns
41–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4565 : rowsJ2 182 183 33 36 ≤ 35146282864661 := by decide +kernel

theorem rows22250R_4566 : rowsJ2 182 183 36 38 ≤ 37764711552578 := by decide +kernel

theorem rows22250R_4567 : rowsJ2 182 183 38 39 ≤ 22030865477169 := by decide +kernel

theorem rows22250R_4568 : rowsJ2 182 183 39 40 ≤ 24235490854111 := by decide +kernel

theorem rows22250R_4569 : rowsJ2 182 183 40 41 ≤ 26516743894525 := by decide +kernel

theorem rows22250R_4570 : rowsJ2 182 183 41 42 ≤ 28873002030630 := by decide +kernel

theorem rows22250R_4571 : rowsJ2 182 183 42 43 ≤ 25921077161581 := by decide +kernel

theorem rows22250R_4572 : rowsJ2 182 183 43 44 ≤ 23158742522942 := by decide +kernel

theorem rows22250R_4573 : rowsJ2 182 183 44 45 ≤ 20578793895300 := by decide +kernel

theorem rows22250R_4574 : rowsJ2 182 183 45 340 ≤ 3461092665425290 := by decide +kernel

theorem rows22250R_4575 : rowsJ2 183 184 0 33 ≤ 20736198119696 := by decide +kernel

theorem rows22250R_4576 : rowsJ2 183 184 33 35 ≤ 22673078935293 := by decide +kernel

theorem rows22250R_4577 : rowsJ2 183 184 35 37 ≤ 35163803069712 := by decide +kernel

theorem rows22250R_4578 : rowsJ2 183 184 37 38 ≤ 21467166353710 := by decide +kernel

theorem rows22250R_4579 : rowsJ2 183 184 38 39 ≤ 23681516906261 := by decide +kernel

theorem rows22250R_4580 : rowsJ2 183 184 39 40 ≤ 25975146823247 := by decide +kernel

theorem rows22250R_4581 : rowsJ2 183 184 40 41 ≤ 28346242310572 := by decide +kernel

theorem rows22250R_4582 : rowsJ2 183 184 41 42 ≤ 28024243546912 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4565
#print axioms SieveCert.rows22250R_4582
