/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 815–825 of 5066

File 82 of 387: the parts `rows22240R_815` … `rows22240R_825` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 96333 in units of a depth-4 test: row 57 columns 53–53, row 57 columns
54–54, row 57 columns 55–55, row 57 columns 56–56, row 57 columns 57–339, row 58 columns 0–15, row 58 columns 16–20,
row 58 columns 21–22, row 58 columns 23–23, row 58 columns 24–24, row 58 columns 25–25), each a sum of refined costs
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

theorem rows22240R_815 : rowsJ2 57 58 53 54 ≤ 7501135793696 := by decide +kernel

theorem rows22240R_816 : rowsJ2 57 58 54 55 ≤ 8954848952193 := by decide +kernel

theorem rows22240R_817 : rowsJ2 57 58 55 56 ≤ 10469813438764 := by decide +kernel

theorem rows22240R_818 : rowsJ2 57 58 56 57 ≤ 12054392296247 := by decide +kernel

theorem rows22240R_819 : rowsJ2 57 58 57 340 ≤ 13458970565845 := by decide +kernel

theorem rows22240R_820 : rowsJ2 58 59 0 16 ≤ 2865462809611 := by decide +kernel

theorem rows22240R_821 : rowsJ2 58 59 16 21 ≤ 1373851670801 := by decide +kernel

theorem rows22240R_822 : rowsJ2 58 59 21 23 ≤ 317784138334 := by decide +kernel

theorem rows22240R_823 : rowsJ2 58 59 23 24 ≤ 121908189914 := by decide +kernel

theorem rows22240R_824 : rowsJ2 58 59 24 25 ≤ 101381367306 := by decide +kernel

theorem rows22240R_825 : rowsJ2 58 59 25 26 ≤ 81075184654 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_815
#print axioms SieveCert.rows22240R_825
