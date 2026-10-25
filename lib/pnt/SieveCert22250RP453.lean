/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5600–5615 of 5796

File 453 of 465: the parts `rows22250R_5600` … `rows22250R_5615` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94485 tests: row 191 columns 0–34, row 191 columns 35–37, row 191 columns
38–38, row 191 columns 39–39, row 191 columns 40–40, row 191 columns 41–41, row 191 columns 42–42, row 191 columns
43–43, row 191 columns 44–44, row 191 columns 45–45, row 191 columns 46–46, row 191 columns 47–47, row 191 columns
48–48, row 191 columns 49–359, row 192 columns 0–34, row 192 columns 35–36), each a sum of refined costs (`rows2` or
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

theorem rows22250R_5600 : rowsJ2 191 192 0 35 ≤ 11745003098222 := by decide +kernel

theorem rows22250R_5601 : rowsJ2 191 192 35 38 ≤ 24937533198882 := by decide +kernel

theorem rows22250R_5602 : rowsJ2 191 192 38 39 ≤ 12870646901483 := by decide +kernel

theorem rows22250R_5603 : rowsJ2 191 192 39 40 ≤ 15578140348358 := by decide +kernel

theorem rows22250R_5604 : rowsJ2 191 192 40 41 ≤ 17252447069452 := by decide +kernel

theorem rows22250R_5605 : rowsJ2 191 192 41 42 ≤ 18989324813085 := by decide +kernel

theorem rows22250R_5606 : rowsJ2 191 192 42 43 ≤ 20787018276046 := by decide +kernel

theorem rows22250R_5607 : rowsJ2 191 192 43 44 ≤ 22644032663602 := by decide +kernel

theorem rows22250R_5608 : rowsJ2 191 192 44 45 ≤ 24559123989001 := by decide +kernel

theorem rows22250R_5609 : rowsJ2 191 192 45 46 ≤ 24300058065340 := by decide +kernel

theorem rows22250R_5610 : rowsJ2 191 192 46 47 ≤ 21934920042008 := by decide +kernel

theorem rows22250R_5611 : rowsJ2 191 192 47 48 ≤ 19713294714558 := by decide +kernel

theorem rows22250R_5612 : rowsJ2 191 192 48 49 ≤ 17630153220112 := by decide +kernel

theorem rows22250R_5613 : rowsJ2 191 192 49 360 ≤ 3042901410836313 := by decide +kernel

theorem rows22250R_5614 : rowsJ2 192 193 0 35 ≤ 13810785931608 := by decide +kernel

theorem rows22250R_5615 : rowsJ2 192 193 35 37 ≤ 16049242580404 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5600
#print axioms SieveCert.rows22250R_5615
