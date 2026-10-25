/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2595–2607 of 5796

File 238 of 465: the parts `rows22250R_2595` … `rows22250R_2607` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 95877 tests: row 94 columns 94–359, row 95 columns 0–16, row 95 columns
17–19, row 95 columns 20–23, row 95 columns 24–28, row 95 columns 29–34, row 95 columns 35–37, row 95 columns 38–39,
row 95 columns 40–40, row 95 columns 41–41, row 95 columns 42–42, row 95 columns 43–43, row 95 columns 44–44), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2595 : rowsJ2 94 95 94 360 ≤ 6832694674581 := by decide +kernel

theorem rows22250R_2596 : rowsJ2 95 96 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_2597 : rowsJ2 95 96 17 20 ≤ 0 := by decide +kernel

theorem rows22250R_2598 : rowsJ2 95 96 20 24 ≤ 0 := by decide +kernel

theorem rows22250R_2599 : rowsJ2 95 96 24 29 ≤ 0 := by decide +kernel

theorem rows22250R_2600 : rowsJ2 95 96 29 35 ≤ 793569698343 := by decide +kernel

theorem rows22250R_2601 : rowsJ2 95 96 35 38 ≤ 5855693912890 := by decide +kernel

theorem rows22250R_2602 : rowsJ2 95 96 38 40 ≤ 9282686813387 := by decide +kernel

theorem rows22250R_2603 : rowsJ2 95 96 40 41 ≤ 6308479613172 := by decide +kernel

theorem rows22250R_2604 : rowsJ2 95 96 41 42 ≤ 7447764235028 := by decide +kernel

theorem rows22250R_2605 : rowsJ2 95 96 42 43 ≤ 8601377990785 := by decide +kernel

theorem rows22250R_2606 : rowsJ2 95 96 43 44 ≤ 9766928533816 := by decide +kernel

theorem rows22250R_2607 : rowsJ2 95 96 44 45 ≤ 10942220658050 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2595
#print axioms SieveCert.rows22250R_2607
