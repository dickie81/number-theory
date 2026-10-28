/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2727–2740 of 5066

File 232 of 387: the parts `rows22240R_2727` … `rows22240R_2740` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 96982 in units of a depth-4 test: row 99 columns 49–50, row 99 columns
51–52, row 99 columns 53–54, row 99 columns 55–57, row 99 columns 58–62, row 99 columns 63–68, row 99 columns 69–73,
row 99 columns 74–77, row 99 columns 78–79, row 99 columns 80–80, row 99 columns 81–81, row 99 columns 82–82, row 99
columns 83–83, row 99 columns 84–84), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2727 : rowsJ2 99 100 49 51 ≤ 8770007642707 := by decide +kernel

theorem rows22240R_2728 : rowsJ2 99 100 51 53 ≤ 5355141554751 := by decide +kernel

theorem rows22240R_2729 : rowsJ2 99 100 53 55 ≤ 2654450309392 := by decide +kernel

theorem rows22240R_2730 : rowsJ2 99 100 55 58 ≤ 684834467437 := by decide +kernel

theorem rows22240R_2731 : rowsJ2 99 100 58 63 ≤ 0 := by decide +kernel

theorem rows22240R_2732 : rowsJ2 99 100 63 69 ≤ 0 := by decide +kernel

theorem rows22240R_2733 : rowsJ2 99 100 69 74 ≤ 0 := by decide +kernel

theorem rows22240R_2734 : rowsJ2 99 100 74 78 ≤ 233762994924 := by decide +kernel

theorem rows22240R_2735 : rowsJ2 99 100 78 80 ≤ 972713150208 := by decide +kernel

theorem rows22240R_2736 : rowsJ2 99 100 80 81 ≤ 926426201016 := by decide +kernel

theorem rows22240R_2737 : rowsJ2 99 100 81 82 ≤ 1391146527670 := by decide +kernel

theorem rows22240R_2738 : rowsJ2 99 100 82 83 ≤ 2030952103092 := by decide +kernel

theorem rows22240R_2739 : rowsJ2 99 100 83 84 ≤ 2543470375959 := by decide +kernel

theorem rows22240R_2740 : rowsJ2 99 100 84 85 ≤ 2456935057695 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2727
#print axioms SieveCert.rows22240R_2740
