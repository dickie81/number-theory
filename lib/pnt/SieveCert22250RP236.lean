/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2572–2587 of 5796

File 236 of 465: the parts `rows22250R_2572` … `rows22250R_2587` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97087 tests: row 94 columns 57–57, row 94 columns 58–58, row 94 columns
59–59, row 94 columns 60–60, row 94 columns 61–61, row 94 columns 62–63, row 94 columns 64–65, row 94 columns 66–67,
row 94 columns 68–70, row 94 columns 71–74, row 94 columns 75–78, row 94 columns 79–81, row 94 columns 82–83, row 94
columns 84–84, row 94 columns 85–85, row 94 columns 86–86), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2572 : rowsJ2 94 95 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2573 : rowsJ2 94 95 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_2574 : rowsJ2 94 95 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_2575 : rowsJ2 94 95 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_2576 : rowsJ2 94 95 61 62 ≤ 0 := by decide +kernel

theorem rows22250R_2577 : rowsJ2 94 95 62 64 ≤ 0 := by decide +kernel

theorem rows22250R_2578 : rowsJ2 94 95 64 66 ≤ 0 := by decide +kernel

theorem rows22250R_2579 : rowsJ2 94 95 66 68 ≤ 0 := by decide +kernel

theorem rows22250R_2580 : rowsJ2 94 95 68 71 ≤ 0 := by decide +kernel

theorem rows22250R_2581 : rowsJ2 94 95 71 75 ≤ 0 := by decide +kernel

theorem rows22250R_2582 : rowsJ2 94 95 75 79 ≤ 0 := by decide +kernel

theorem rows22250R_2583 : rowsJ2 94 95 79 82 ≤ 213361052369 := by decide +kernel

theorem rows22250R_2584 : rowsJ2 94 95 82 84 ≤ 888113048292 := by decide +kernel

theorem rows22250R_2585 : rowsJ2 94 95 84 85 ≤ 845191619110 := by decide +kernel

theorem rows22250R_2586 : rowsJ2 94 95 85 86 ≤ 1185491266592 := by decide +kernel

theorem rows22250R_2587 : rowsJ2 94 95 86 87 ≤ 1588522229541 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2572
#print axioms SieveCert.rows22250R_2587
