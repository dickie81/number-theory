/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3450–3466 of 5796

File 300 of 465: the parts `rows22250R_3450` … `rows22250R_3466` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 94044 tests: row 112 columns 83–83, row 112 columns 84–84, row 112 columns
85–85, row 112 columns 86–86, row 112 columns 87–87, row 112 columns 88–89, row 112 columns 90–91, row 112 columns
92–93, row 112 columns 94–95, row 112 columns 96–97, row 112 columns 98–98, row 112 columns 99–99, row 112 columns
100–100, row 112 columns 101–101, row 112 columns 102–102, row 112 columns 103–103, row 112 columns 104–104), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22250R_3450 : rowsJ2 112 113 83 84 ≤ 490391091585 := by decide +kernel

theorem rows22250R_3451 : rowsJ2 112 113 84 85 ≤ 743311952942 := by decide +kernel

theorem rows22250R_3452 : rowsJ2 112 113 85 86 ≤ 655952138417 := by decide +kernel

theorem rows22250R_3453 : rowsJ2 112 113 86 87 ≤ 579950684445 := by decide +kernel

theorem rows22250R_3454 : rowsJ2 112 113 87 88 ≤ 536520247214 := by decide +kernel

theorem rows22250R_3455 : rowsJ2 112 113 88 90 ≤ 1147503926043 := by decide +kernel

theorem rows22250R_3456 : rowsJ2 112 113 90 92 ≤ 1645429946440 := by decide +kernel

theorem rows22250R_3457 : rowsJ2 112 113 92 94 ≤ 2630764975990 := by decide +kernel

theorem rows22250R_3458 : rowsJ2 112 113 94 96 ≤ 4122996182849 := by decide +kernel

theorem rows22250R_3459 : rowsJ2 112 113 96 98 ≤ 6144659522647 := by decide +kernel

theorem rows22250R_3460 : rowsJ2 112 113 98 99 ≤ 3999613830851 := by decide +kernel

theorem rows22250R_3461 : rowsJ2 112 113 99 100 ≤ 4722022904283 := by decide +kernel

theorem rows22250R_3462 : rowsJ2 112 113 100 101 ≤ 5505338254795 := by decide +kernel

theorem rows22250R_3463 : rowsJ2 112 113 101 102 ≤ 6378167236015 := by decide +kernel

theorem rows22250R_3464 : rowsJ2 112 113 102 103 ≤ 7302383468661 := by decide +kernel

theorem rows22250R_3465 : rowsJ2 112 113 103 104 ≤ 8320848894634 := by decide +kernel

theorem rows22250R_3466 : rowsJ2 112 113 104 105 ≤ 9394759892612 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3450
#print axioms SieveCert.rows22250R_3466
