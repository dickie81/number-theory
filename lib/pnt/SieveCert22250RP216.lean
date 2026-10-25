/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2668–2686 of 4715

File 216 of 351: the parts `rows22250R_2668` … `rows22250R_2686` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (19 parts, 96019 tests: row 101 columns 73–76, row 101 columns 77–78, row 101 columns
79–79, row 101 columns 80–80, row 101 columns 81–81, row 101 columns 82–82, row 101 columns 83–83, row 101 columns
84–84, row 101 columns 85–85, row 101 columns 86–86, row 101 columns 87–87, row 101 columns 88–88, row 101 columns
89–89, row 101 columns 90–90, row 101 columns 91–91, row 101 columns 92–92, row 101 columns 93–93, row 101 columns
94–94, row 101 columns 95–95), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_2668 : rowsJ2 101 102 73 77 ≤ 107561806274 := by decide +kernel

theorem rows22250R_2669 : rowsJ2 101 102 77 79 ≤ 702396862399 := by decide +kernel

theorem rows22250R_2670 : rowsJ2 101 102 79 80 ≤ 741467296248 := by decide +kernel

theorem rows22250R_2671 : rowsJ2 101 102 80 81 ≤ 1084002751944 := by decide +kernel

theorem rows22250R_2672 : rowsJ2 101 102 81 82 ≤ 1499916201466 := by decide +kernel

theorem rows22250R_2673 : rowsJ2 101 102 82 83 ≤ 1653123915710 := by decide +kernel

theorem rows22250R_2674 : rowsJ2 101 102 83 84 ≤ 1515723201182 := by decide +kernel

theorem rows22250R_2675 : rowsJ2 101 102 84 85 ≤ 1376703714176 := by decide +kernel

theorem rows22250R_2676 : rowsJ2 101 102 85 86 ≤ 1291487919146 := by decide +kernel

theorem rows22250R_2677 : rowsJ2 101 102 86 87 ≤ 1286230111904 := by decide +kernel

theorem rows22250R_2678 : rowsJ2 101 102 87 88 ≤ 1379348059983 := by decide +kernel

theorem rows22250R_2679 : rowsJ2 101 102 88 89 ≤ 1558100089530 := by decide +kernel

theorem rows22250R_2680 : rowsJ2 101 102 89 90 ≤ 1794491521060 := by decide +kernel

theorem rows22250R_2681 : rowsJ2 101 102 90 91 ≤ 2119532942994 := by decide +kernel

theorem rows22250R_2682 : rowsJ2 101 102 91 92 ≤ 2506170848737 := by decide +kernel

theorem rows22250R_2683 : rowsJ2 101 102 92 93 ≤ 2985136208298 := by decide +kernel

theorem rows22250R_2684 : rowsJ2 101 102 93 94 ≤ 3528805931812 := by decide +kernel

theorem rows22250R_2685 : rowsJ2 101 102 94 95 ≤ 4169016645751 := by decide +kernel

theorem rows22250R_2686 : rowsJ2 101 102 95 96 ≤ 4877556930572 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2668
#print axioms SieveCert.rows22250R_2686
