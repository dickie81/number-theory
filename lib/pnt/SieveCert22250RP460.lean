/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5710–5724 of 5796

File 460 of 465: the parts `rows22250R_5710` … `rows22250R_5724` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98738 tests: row 202 columns 32–34, row 202 columns 35–36, row 202 columns
37–37, row 202 columns 38–359, row 203 columns 0–31, row 203 columns 32–33, row 203 columns 34–35, row 203 columns
36–36, row 203 columns 37–359, row 204 columns 0–30, row 204 columns 31–33, row 204 columns 34–35, row 204 columns
36–359, row 205 columns 0–30, row 205 columns 31–33), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_5710 : rowsJ2 202 203 32 35 ≤ 33843837914339 := by decide +kernel

theorem rows22250R_5711 : rowsJ2 202 203 35 37 ≤ 37341067973619 := by decide +kernel

theorem rows22250R_5712 : rowsJ2 202 203 37 38 ≤ 24098526978697 := by decide +kernel

theorem rows22250R_5713 : rowsJ2 202 203 38 360 ≤ 4335854401864511 := by decide +kernel

theorem rows22250R_5714 : rowsJ2 203 204 0 32 ≤ 21174337530697 := by decide +kernel

theorem rows22250R_5715 : rowsJ2 203 204 32 34 ≤ 21889079741695 := by decide +kernel

theorem rows22250R_5716 : rowsJ2 203 204 34 36 ≤ 33438263508526 := by decide +kernel

theorem rows22250R_5717 : rowsJ2 203 204 36 37 ≤ 21881859291130 := by decide +kernel

theorem rows22250R_5718 : rowsJ2 203 204 37 360 ≤ 4445334951543101 := by decide +kernel

theorem rows22250R_5719 : rowsJ2 204 205 0 31 ≤ 16225533145525 := by decide +kernel

theorem rows22250R_5720 : rowsJ2 204 205 31 34 ≤ 32213844895799 := by decide +kernel

theorem rows22250R_5721 : rowsJ2 204 205 34 36 ≤ 36122580307148 := by decide +kernel

theorem rows22250R_5722 : rowsJ2 204 205 36 360 ≤ 4554089926067753 := by decide +kernel

theorem rows22250R_5723 : rowsJ2 205 206 0 31 ≤ 19013203026031 := by decide +kernel

theorem rows22250R_5724 : rowsJ2 205 206 31 34 ≤ 35297336246532 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5710
#print axioms SieveCert.rows22250R_5724
