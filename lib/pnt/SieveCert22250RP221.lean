/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2753–2769 of 4715

File 221 of 351: the parts `rows22250R_2753` … `rows22250R_2769` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 97424 in units of a depth-4 test: row 103 columns 78–79, row 103
columns 80–80, row 103 columns 81–81, row 103 columns 82–82, row 103 columns 83–83, row 103 columns 84–84, row 103
columns 85–85, row 103 columns 86–87, row 103 columns 88–89, row 103 columns 90–91, row 103 columns 92–93, row 103
columns 94–95, row 103 columns 96–96, row 103 columns 97–97, row 103 columns 98–98, row 103 columns 99–99, row 103
columns 100–100), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2753 : rowsJ2 103 104 78 80 ≤ 1180687035444 := by decide +kernel

theorem rows22250R_2754 : rowsJ2 103 104 80 81 ≤ 1067662648092 := by decide +kernel

theorem rows22250R_2755 : rowsJ2 103 104 81 82 ≤ 1203103907414 := by decide +kernel

theorem rows22250R_2756 : rowsJ2 103 104 82 83 ≤ 1079557864203 := by decide +kernel

theorem rows22250R_2757 : rowsJ2 103 104 83 84 ≤ 969012541550 := by decide +kernel

theorem rows22250R_2758 : rowsJ2 103 104 84 85 ≤ 897557261296 := by decide +kernel

theorem rows22250R_2759 : rowsJ2 103 104 85 86 ≤ 924740244088 := by decide +kernel

theorem rows22250R_2760 : rowsJ2 103 104 86 88 ≤ 2247359315768 := by decide +kernel

theorem rows22250R_2761 : rowsJ2 103 104 88 90 ≤ 3260490983162 := by decide +kernel

theorem rows22250R_2762 : rowsJ2 103 104 90 92 ≤ 4889635996261 := by decide +kernel

theorem rows22250R_2763 : rowsJ2 103 104 92 94 ≤ 7162955301349 := by decide +kernel

theorem rows22250R_2764 : rowsJ2 103 104 94 96 ≤ 10113018165474 := by decide +kernel

theorem rows22250R_2765 : rowsJ2 103 104 96 97 ≤ 6388507574355 := by decide +kernel

theorem rows22250R_2766 : rowsJ2 103 104 97 98 ≤ 7388770991674 := by decide +kernel

theorem rows22250R_2767 : rowsJ2 103 104 98 99 ≤ 8501769802621 := by decide +kernel

theorem rows22250R_2768 : rowsJ2 103 104 99 100 ≤ 9696870338641 := by decide +kernel

theorem rows22250R_2769 : rowsJ2 103 104 100 101 ≤ 11011561782244 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2753
#print axioms SieveCert.rows22250R_2769
