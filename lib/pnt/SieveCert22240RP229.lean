/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2684–2697 of 5066

File 229 of 387: the parts `rows22240R_2684` … `rows22240R_2697` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 98344 in units of a depth-4 test: row 98 columns 52–53, row 98 columns
54–55, row 98 columns 56–58, row 98 columns 59–63, row 98 columns 64–69, row 98 columns 70–74, row 98 columns 75–77,
row 98 columns 78–79, row 98 columns 80–80, row 98 columns 81–81, row 98 columns 82–82, row 98 columns 83–83, row 98
columns 84–84, row 98 columns 85–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_2684 : rowsJ2 98 99 52 54 ≤ 4787532830860 := by decide +kernel

theorem rows22240R_2685 : rowsJ2 98 99 54 56 ≤ 2107023425331 := by decide +kernel

theorem rows22240R_2686 : rowsJ2 98 99 56 59 ≤ 420567999817 := by decide +kernel

theorem rows22240R_2687 : rowsJ2 98 99 59 64 ≤ 0 := by decide +kernel

theorem rows22240R_2688 : rowsJ2 98 99 64 70 ≤ 0 := by decide +kernel

theorem rows22240R_2689 : rowsJ2 98 99 70 75 ≤ 0 := by decide +kernel

theorem rows22240R_2690 : rowsJ2 98 99 75 78 ≤ 235928007290 := by decide +kernel

theorem rows22240R_2691 : rowsJ2 98 99 78 80 ≤ 981638087384 := by decide +kernel

theorem rows22240R_2692 : rowsJ2 98 99 80 81 ≤ 934665026659 := by decide +kernel

theorem rows22240R_2693 : rowsJ2 98 99 81 82 ≤ 1399382538416 := by decide +kernel

theorem rows22240R_2694 : rowsJ2 98 99 82 83 ≤ 2035901460932 := by decide +kernel

theorem rows22240R_2695 : rowsJ2 98 99 83 84 ≤ 2743058996733 := by decide +kernel

theorem rows22240R_2696 : rowsJ2 98 99 84 85 ≤ 3242344291261 := by decide +kernel

theorem rows22240R_2697 : rowsJ2 98 99 85 86 ≤ 2679158388454 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2684
#print axioms SieveCert.rows22240R_2697
