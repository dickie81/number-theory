/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 667–677 of 5066

File 68 of 387: the parts `rows22240R_667` … `rows22240R_677` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 96826 in units of a depth-4 test: row 53 columns 44–44, row 53 columns
45–45, row 53 columns 46–46, row 53 columns 47–47, row 53 columns 48–48, row 53 columns 49–49, row 53 columns 50–50,
row 53 columns 51–51, row 53 columns 52–52, row 53 columns 53–339, row 54 columns 0–14), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_667 : rowsJ2 53 54 44 45 ≤ 74878226056 := by decide +kernel

theorem rows22240R_668 : rowsJ2 53 54 45 46 ≤ 218977037741 := by decide +kernel

theorem rows22240R_669 : rowsJ2 53 54 46 47 ≤ 427035910078 := by decide +kernel

theorem rows22240R_670 : rowsJ2 53 54 47 48 ≤ 911757187745 := by decide +kernel

theorem rows22240R_671 : rowsJ2 53 54 48 49 ≤ 1741911883339 := by decide +kernel

theorem rows22240R_672 : rowsJ2 53 54 49 50 ≤ 2686256734722 := by decide +kernel

theorem rows22240R_673 : rowsJ2 53 54 50 51 ≤ 3665377055703 := by decide +kernel

theorem rows22240R_674 : rowsJ2 53 54 51 52 ≤ 4822718073317 := by decide +kernel

theorem rows22240R_675 : rowsJ2 53 54 52 53 ≤ 6303505045480 := by decide +kernel

theorem rows22240R_676 : rowsJ2 53 54 53 340 ≤ 7802267360947 := by decide +kernel

theorem rows22240R_677 : rowsJ2 54 55 0 15 ≤ 2476087595731 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_667
#print axioms SieveCert.rows22240R_677
