/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2786–2801 of 4715

File 223 of 351: the parts `rows22250R_2786` … `rows22250R_2801` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 99839 in units of a depth-4 test: row 104 columns 55–64, row 104
columns 65–71, row 104 columns 72–75, row 104 columns 76–77, row 104 columns 78–79, row 104 columns 80–80, row 104
columns 81–81, row 104 columns 82–82, row 104 columns 83–83, row 104 columns 84–85, row 104 columns 86–87, row 104
columns 88–89, row 104 columns 90–91, row 104 columns 92–93, row 104 columns 94–95, row 104 columns 96–96), each a
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

theorem rows22250R_2786 : rowsJ2 104 105 55 65 ≤ 0 := by decide +kernel

theorem rows22250R_2787 : rowsJ2 104 105 65 72 ≤ 0 := by decide +kernel

theorem rows22250R_2788 : rowsJ2 104 105 72 76 ≤ 15127970832 := by decide +kernel

theorem rows22250R_2789 : rowsJ2 104 105 76 78 ≤ 330317917962 := by decide +kernel

theorem rows22250R_2790 : rowsJ2 104 105 78 80 ≤ 1171791822406 := by decide +kernel

theorem rows22250R_2791 : rowsJ2 104 105 80 81 ≤ 1058399687201 := by decide +kernel

theorem rows22250R_2792 : rowsJ2 104 105 81 82 ≤ 950261486653 := by decide +kernel

theorem rows22250R_2793 : rowsJ2 104 105 82 83 ≤ 839478074105 := by decide +kernel

theorem rows22250R_2794 : rowsJ2 104 105 83 84 ≤ 741681996858 := by decide +kernel

theorem rows22250R_2795 : rowsJ2 104 105 84 86 ≤ 1541516669566 := by decide +kernel

theorem rows22250R_2796 : rowsJ2 104 105 86 88 ≤ 2122880432452 := by decide +kernel

theorem rows22250R_2797 : rowsJ2 104 105 88 90 ≤ 3307348478416 := by decide +kernel

theorem rows22250R_2798 : rowsJ2 104 105 90 92 ≤ 5121789594491 := by decide +kernel

theorem rows22250R_2799 : rowsJ2 104 105 92 94 ≤ 7595940887253 := by decide +kernel

theorem rows22250R_2800 : rowsJ2 104 105 94 96 ≤ 10764160602832 := by decide +kernel

theorem rows22250R_2801 : rowsJ2 104 105 96 97 ≤ 6789205203088 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2786
#print axioms SieveCert.rows22250R_2801
