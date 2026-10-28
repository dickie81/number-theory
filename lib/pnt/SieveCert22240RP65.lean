/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 637–648 of 5066

File 65 of 387: the parts `rows22240R_637` … `rows22240R_648` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 97421 in units of a depth-4 test: row 52 columns 46–46, row 52 columns
47–47, row 52 columns 48–48, row 52 columns 49–49, row 52 columns 50–50, row 52 columns 51–51, row 52 columns
52–339, row 53 columns 0–14, row 53 columns 15–19, row 53 columns 20–22, row 53 columns 23–24, row 53 columns
25–25), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_637 : rowsJ2 52 53 46 47 ≤ 431365182213 := by decide +kernel

theorem rows22240R_638 : rowsJ2 52 53 47 48 ≤ 921000543856 := by decide +kernel

theorem rows22240R_639 : rowsJ2 52 53 48 49 ≤ 1759571312921 := by decide +kernel

theorem rows22240R_640 : rowsJ2 52 53 49 50 ≤ 2713489892778 := by decide +kernel

theorem rows22240R_641 : rowsJ2 52 53 50 51 ≤ 3702536494486 := by decide +kernel

theorem rows22240R_642 : rowsJ2 52 53 51 52 ≤ 4871610586777 := by decide +kernel

theorem rows22240R_643 : rowsJ2 52 53 52 340 ≤ 6367409715122 := by decide +kernel

theorem rows22240R_644 : rowsJ2 53 54 0 15 ≤ 2441779357997 := by decide +kernel

theorem rows22240R_645 : rowsJ2 53 54 15 20 ≤ 2574698016239 := by decide +kernel

theorem rows22240R_646 : rowsJ2 53 54 20 23 ≤ 1037315588596 := by decide +kernel

theorem rows22240R_647 : rowsJ2 53 54 23 25 ≤ 493288713706 := by decide +kernel

theorem rows22240R_648 : rowsJ2 53 54 25 26 ≤ 197739399644 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_637
#print axioms SieveCert.rows22240R_648
