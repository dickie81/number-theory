/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2731–2737 of 5796

File 249 of 465: the parts `rows22250R_2731` … `rows22250R_2737` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 92760 tests: row 97 columns 87–87, row 97 columns 88–88, row 97 columns
89–89, row 97 columns 90–90, row 97 columns 91–91, row 97 columns 92–92, row 97 columns 93–93), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2731 : rowsJ2 97 98 87 88 ≤ 2059475275827 := by decide +kernel

theorem rows22250R_2732 : rowsJ2 97 98 88 89 ≤ 2696023526301 := by decide +kernel

theorem rows22250R_2733 : rowsJ2 97 98 89 90 ≤ 3461006158150 := by decide +kernel

theorem rows22250R_2734 : rowsJ2 97 98 90 91 ≤ 4377068842272 := by decide +kernel

theorem rows22250R_2735 : rowsJ2 97 98 91 92 ≤ 5204908910393 := by decide +kernel

theorem rows22250R_2736 : rowsJ2 97 98 92 93 ≤ 5257563063152 := by decide +kernel

theorem rows22250R_2737 : rowsJ2 97 98 93 94 ≤ 4687352509340 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2731
#print axioms SieveCert.rows22250R_2737
