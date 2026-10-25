/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2621–2636 of 5796

File 240 of 465: the parts `rows22250R_2621` … `rows22250R_2636` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 95616 tests: row 95 columns 58–58, row 95 columns 59–59, row 95 columns
60–60, row 95 columns 61–62, row 95 columns 63–64, row 95 columns 65–66, row 95 columns 67–69, row 95 columns 70–73,
row 95 columns 74–77, row 95 columns 78–80, row 95 columns 81–82, row 95 columns 83–83, row 95 columns 84–84, row 95
columns 85–85, row 95 columns 86–86, row 95 columns 87–87), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_2621 : rowsJ2 95 96 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_2622 : rowsJ2 95 96 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_2623 : rowsJ2 95 96 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_2624 : rowsJ2 95 96 61 63 ≤ 0 := by decide +kernel

theorem rows22250R_2625 : rowsJ2 95 96 63 65 ≤ 0 := by decide +kernel

theorem rows22250R_2626 : rowsJ2 95 96 65 67 ≤ 0 := by decide +kernel

theorem rows22250R_2627 : rowsJ2 95 96 67 70 ≤ 0 := by decide +kernel

theorem rows22250R_2628 : rowsJ2 95 96 70 74 ≤ 0 := by decide +kernel

theorem rows22250R_2629 : rowsJ2 95 96 74 78 ≤ 0 := by decide +kernel

theorem rows22250R_2630 : rowsJ2 95 96 78 81 ≤ 53135280705 := by decide +kernel

theorem rows22250R_2631 : rowsJ2 95 96 81 83 ≤ 488509966111 := by decide +kernel

theorem rows22250R_2632 : rowsJ2 95 96 83 84 ≤ 552221922490 := by decide +kernel

theorem rows22250R_2633 : rowsJ2 95 96 84 85 ≤ 839354609753 := by decide +kernel

theorem rows22250R_2634 : rowsJ2 95 96 85 86 ≤ 1177304101154 := by decide +kernel

theorem rows22250R_2635 : rowsJ2 95 96 86 87 ≤ 1576536603427 := by decide +kernel

theorem rows22250R_2636 : rowsJ2 95 96 87 88 ≤ 2085209859023 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2621
#print axioms SieveCert.rows22250R_2636
