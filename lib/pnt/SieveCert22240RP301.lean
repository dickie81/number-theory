/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3795–3807 of 5066

File 301 of 387: the parts `rows22240R_3795` … `rows22240R_3807` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 97939 in units of a depth-4 test: row 132 columns 57–57, row 132
columns 58–58, row 132 columns 59–59, row 132 columns 60–60, row 132 columns 61–61, row 132 columns 62–62, row 132
columns 63–63, row 132 columns 64–64, row 132 columns 65–65, row 132 columns 66–66, row 132 columns 67–67, row 132
columns 68–68, row 132 columns 69–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_3795 : rowsJ2 132 133 57 58 ≤ 3765902809919 := by decide +kernel

theorem rows22240R_3796 : rowsJ2 132 133 58 59 ≤ 4416341669941 := by decide +kernel

theorem rows22240R_3797 : rowsJ2 132 133 59 60 ≤ 5108680090095 := by decide +kernel

theorem rows22240R_3798 : rowsJ2 132 133 60 61 ≤ 5841187158894 := by decide +kernel

theorem rows22240R_3799 : rowsJ2 132 133 61 62 ≤ 6591252919388 := by decide +kernel

theorem rows22240R_3800 : rowsJ2 132 133 62 63 ≤ 7295214885135 := by decide +kernel

theorem rows22240R_3801 : rowsJ2 132 133 63 64 ≤ 7931596295019 := by decide +kernel

theorem rows22240R_3802 : rowsJ2 132 133 64 65 ≤ 8521205892150 := by decide +kernel

theorem rows22240R_3803 : rowsJ2 132 133 65 66 ≤ 9042171689257 := by decide +kernel

theorem rows22240R_3804 : rowsJ2 132 133 66 67 ≤ 9515366767256 := by decide +kernel

theorem rows22240R_3805 : rowsJ2 132 133 67 68 ≤ 9918470113780 := by decide +kernel

theorem rows22240R_3806 : rowsJ2 132 133 68 69 ≤ 8941903476182 := by decide +kernel

theorem rows22240R_3807 : rowsJ2 132 133 69 70 ≤ 8014208631232 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3795
#print axioms SieveCert.rows22240R_3807
