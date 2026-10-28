/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2741–2755 of 5066

File 233 of 387: the parts `rows22240R_2741` … `rows22240R_2755` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 98738 in units of a depth-4 test: row 99 columns 85–85, row 99 columns
86–86, row 99 columns 87–87, row 99 columns 88–88, row 99 columns 89–89, row 99 columns 90–90, row 99 columns 91–91,
row 99 columns 92–92, row 99 columns 93–93, row 99 columns 94–94, row 99 columns 95–95, row 99 columns 96–96, row 99
columns 97–97, row 99 columns 98–98, row 99 columns 99–339), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2741 : rowsJ2 99 100 85 86 ≤ 2286230495521 := by decide +kernel

theorem rows22240R_2742 : rowsJ2 99 100 86 87 ≤ 2205862369857 := by decide +kernel

theorem rows22240R_2743 : rowsJ2 99 100 87 88 ≤ 2201716132433 := by decide +kernel

theorem rows22240R_2744 : rowsJ2 99 100 88 89 ≤ 2291711656652 := by decide +kernel

theorem rows22240R_2745 : rowsJ2 99 100 89 90 ≤ 2461886049465 := by decide +kernel

theorem rows22240R_2746 : rowsJ2 99 100 90 91 ≤ 2730771382137 := by decide +kernel

theorem rows22240R_2747 : rowsJ2 99 100 91 92 ≤ 3039949672421 := by decide +kernel

theorem rows22240R_2748 : rowsJ2 99 100 92 93 ≤ 3450962395448 := by decide +kernel

theorem rows22240R_2749 : rowsJ2 99 100 93 94 ≤ 3904480128460 := by decide +kernel

theorem rows22240R_2750 : rowsJ2 99 100 94 95 ≤ 4463553709082 := by decide +kernel

theorem rows22240R_2751 : rowsJ2 99 100 95 96 ≤ 5068038759545 := by decide +kernel

theorem rows22240R_2752 : rowsJ2 99 100 96 97 ≤ 5782668445165 := by decide +kernel

theorem rows22240R_2753 : rowsJ2 99 100 97 98 ≤ 6546254441125 := by decide +kernel

theorem rows22240R_2754 : rowsJ2 99 100 98 99 ≤ 7425142801552 := by decide +kernel

theorem rows22240R_2755 : rowsJ2 99 100 99 340 ≤ 8357067581230 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2741
#print axioms SieveCert.rows22240R_2755
