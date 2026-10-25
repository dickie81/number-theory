/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2620–2633 of 4715

File 213 of 351: the parts `rows22250R_2620` … `rows22250R_2633` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 95293 tests: row 100 columns 47–48, row 100 columns 49–50, row 100 columns
51–53, row 100 columns 54–58, row 100 columns 59–67, row 100 columns 68–73, row 100 columns 74–77, row 100 columns
78–79, row 100 columns 80–80, row 100 columns 81–81, row 100 columns 82–82, row 100 columns 83–83, row 100 columns
84–84, row 100 columns 85–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_2620 : rowsJ2 100 101 47 49 ≤ 7876908551002 := by decide +kernel

theorem rows22250R_2621 : rowsJ2 100 101 49 51 ≤ 4314936867524 := by decide +kernel

theorem rows22250R_2622 : rowsJ2 100 101 51 54 ≤ 2552077904946 := by decide +kernel

theorem rows22250R_2623 : rowsJ2 100 101 54 59 ≤ 185114304426 := by decide +kernel

theorem rows22250R_2624 : rowsJ2 100 101 59 68 ≤ 0 := by decide +kernel

theorem rows22250R_2625 : rowsJ2 100 101 68 74 ≤ 0 := by decide +kernel

theorem rows22250R_2626 : rowsJ2 100 101 74 78 ≤ 354843721778 := by decide +kernel

theorem rows22250R_2627 : rowsJ2 100 101 78 80 ≤ 1208381541985 := by decide +kernel

theorem rows22250R_2628 : rowsJ2 100 101 80 81 ≤ 1092405203045 := by decide +kernel

theorem rows22250R_2629 : rowsJ2 100 101 81 82 ≤ 1510839700270 := by decide +kernel

theorem rows22250R_2630 : rowsJ2 100 101 82 83 ≤ 1987512029548 := by decide +kernel

theorem rows22250R_2631 : rowsJ2 100 101 83 84 ≤ 1837321107301 := by decide +kernel

theorem rows22250R_2632 : rowsJ2 100 101 84 85 ≤ 1684101457569 := by decide +kernel

theorem rows22250R_2633 : rowsJ2 100 101 85 86 ≤ 1545385105321 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2620
#print axioms SieveCert.rows22250R_2633
