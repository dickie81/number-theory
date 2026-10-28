/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1631–1639 of 5066

File 151 of 387: the parts `rows22240R_1631` … `rows22240R_1639` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 94414 in units of a depth-4 test: row 75 columns 52–52, row 75 columns
53–53, row 75 columns 54–54, row 75 columns 55–55, row 75 columns 56–56, row 75 columns 57–57, row 75 columns 58–58,
row 75 columns 59–59, row 75 columns 60–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_1631 : rowsJ2 75 76 52 53 ≤ 3385171901417 := by decide +kernel

theorem rows22240R_1632 : rowsJ2 75 76 53 54 ≤ 3634602650279 := by decide +kernel

theorem rows22240R_1633 : rowsJ2 75 76 54 55 ≤ 3534444140863 := by decide +kernel

theorem rows22240R_1634 : rowsJ2 75 76 55 56 ≤ 3250965932383 := by decide +kernel

theorem rows22240R_1635 : rowsJ2 75 76 56 57 ≤ 2970584813404 := by decide +kernel

theorem rows22240R_1636 : rowsJ2 75 76 57 58 ≤ 2683504209003 := by decide +kernel

theorem rows22240R_1637 : rowsJ2 75 76 58 59 ≤ 2399287483182 := by decide +kernel

theorem rows22240R_1638 : rowsJ2 75 76 59 60 ≤ 2171013044962 := by decide +kernel

theorem rows22240R_1639 : rowsJ2 75 76 60 61 ≤ 1944932461295 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1631
#print axioms SieveCert.rows22240R_1639
