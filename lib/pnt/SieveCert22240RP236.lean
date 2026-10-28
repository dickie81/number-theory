/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2785–2800 of 5066

File 236 of 387: the parts `rows22240R_2785` … `rows22240R_2800` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96694 in units of a depth-4 test: row 100 columns 85–85, row 100
columns 86–86, row 100 columns 87–87, row 100 columns 88–88, row 100 columns 89–89, row 100 columns 90–90, row 100
columns 91–91, row 100 columns 92–92, row 100 columns 93–93, row 100 columns 94–94, row 100 columns 95–95, row 100
columns 96–96, row 100 columns 97–97, row 100 columns 98–98, row 100 columns 99–99, row 100 columns 100–339), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2785 : rowsJ2 100 101 85 86 ≤ 1965073823332 := by decide +kernel

theorem rows22240R_2786 : rowsJ2 100 101 86 87 ≤ 1938349197315 := by decide +kernel

theorem rows22240R_2787 : rowsJ2 100 101 87 88 ≤ 1990054334420 := by decide +kernel

theorem rows22240R_2788 : rowsJ2 100 101 88 89 ≤ 2138140131305 := by decide +kernel

theorem rows22240R_2789 : rowsJ2 100 101 89 90 ≤ 2368920506467 := by decide +kernel

theorem rows22240R_2790 : rowsJ2 100 101 90 91 ≤ 2656348511837 := by decide +kernel

theorem rows22240R_2791 : rowsJ2 100 101 91 92 ≤ 3029286003180 := by decide +kernel

theorem rows22240R_2792 : rowsJ2 100 101 92 93 ≤ 3461270921943 := by decide +kernel

theorem rows22240R_2793 : rowsJ2 100 101 93 94 ≤ 3982170048342 := by decide +kernel

theorem rows22240R_2794 : rowsJ2 100 101 94 95 ≤ 4565217884570 := by decide +kernel

theorem rows22240R_2795 : rowsJ2 100 101 95 96 ≤ 5241442551093 := by decide +kernel

theorem rows22240R_2796 : rowsJ2 100 101 96 97 ≤ 5983562018960 := by decide +kernel

theorem rows22240R_2797 : rowsJ2 100 101 97 98 ≤ 6823679350780 := by decide +kernel

theorem rows22240R_2798 : rowsJ2 100 101 98 99 ≤ 7733978480034 := by decide +kernel

theorem rows22240R_2799 : rowsJ2 100 101 99 100 ≤ 8747717691562 := by decide +kernel

theorem rows22240R_2800 : rowsJ2 100 101 100 340 ≤ 9836532236819 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2785
#print axioms SieveCert.rows22240R_2800
