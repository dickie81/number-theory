/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4806–4822 of 5066

File 372 of 387: the parts `rows22240R_4806` … `rows22240R_4822` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 99104 in units of a depth-4 test: row 175 columns 36–37, row 175
columns 38–39, row 175 columns 40–40, row 175 columns 41–41, row 175 columns 42–42, row 175 columns 43–43, row 175
columns 44–44, row 175 columns 45–45, row 175 columns 46–46, row 175 columns 47–47, row 175 columns 48–48, row 175
columns 49–49, row 175 columns 50–50, row 175 columns 51–52, row 175 columns 53–339, row 176 columns 0–35, row 176
columns 36–37), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4806 : rowsJ2 175 176 36 38 ≤ 18381310295866 := by decide +kernel

theorem rows22240R_4807 : rowsJ2 175 176 38 40 ≤ 25320236611868 := by decide +kernel

theorem rows22240R_4808 : rowsJ2 175 176 40 41 ≤ 15125054995717 := by decide +kernel

theorem rows22240R_4809 : rowsJ2 175 176 41 42 ≤ 16865387384931 := by decide +kernel

theorem rows22240R_4810 : rowsJ2 175 176 42 43 ≤ 18675327109663 := by decide +kernel

theorem rows22240R_4811 : rowsJ2 175 176 43 44 ≤ 20552717856969 := by decide +kernel

theorem rows22240R_4812 : rowsJ2 175 176 44 45 ≤ 22495704783516 := by decide +kernel

theorem rows22240R_4813 : rowsJ2 175 176 45 46 ≤ 24502722046692 := by decide +kernel

theorem rows22240R_4814 : rowsJ2 175 176 46 47 ≤ 24238231335657 := by decide +kernel

theorem rows22240R_4815 : rowsJ2 175 176 47 48 ≤ 21774987430043 := by decide +kernel

theorem rows22240R_4816 : rowsJ2 175 176 48 49 ≤ 19466867416404 := by decide +kernel

theorem rows22240R_4817 : rowsJ2 175 176 49 50 ≤ 17308441633271 := by decide +kernel

theorem rows22240R_4818 : rowsJ2 175 176 50 51 ≤ 15294708827256 := by decide +kernel

theorem rows22240R_4819 : rowsJ2 175 176 51 53 ≤ 25104340600275 := by decide +kernel

theorem rows22240R_4820 : rowsJ2 175 176 53 340 ≤ 2796047502905204 := by decide +kernel

theorem rows22240R_4821 : rowsJ2 176 177 0 36 ≤ 18512327020990 := by decide +kernel

theorem rows22240R_4822 : rowsJ2 176 177 36 38 ≤ 20233843656356 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4806
#print axioms SieveCert.rows22240R_4822
