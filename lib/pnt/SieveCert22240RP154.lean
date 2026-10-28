/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1674–1683 of 5066

File 154 of 387: the parts `rows22240R_1674` … `rows22240R_1683` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 93000 in units of a depth-4 test: row 76 columns 45–45, row 76 columns
46–46, row 76 columns 47–47, row 76 columns 48–48, row 76 columns 49–49, row 76 columns 50–50, row 76 columns 51–51,
row 76 columns 52–52, row 76 columns 53–53, row 76 columns 54–54), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1674 : rowsJ2 76 77 45 46 ≤ 177909811371 := by decide +kernel

theorem rows22240R_1675 : rowsJ2 76 77 46 47 ≤ 346949063675 := by decide +kernel

theorem rows22240R_1676 : rowsJ2 76 77 47 48 ≤ 740765109265 := by decide +kernel

theorem rows22240R_1677 : rowsJ2 76 77 48 49 ≤ 1415231559380 := by decide +kernel

theorem rows22240R_1678 : rowsJ2 76 77 49 50 ≤ 1981431087727 := by decide +kernel

theorem rows22240R_1679 : rowsJ2 76 77 50 51 ≤ 2378081625715 := by decide +kernel

theorem rows22240R_1680 : rowsJ2 76 77 51 52 ≤ 2673104587307 := by decide +kernel

theorem rows22240R_1681 : rowsJ2 76 77 52 53 ≤ 3037600941642 := by decide +kernel

theorem rows22240R_1682 : rowsJ2 76 77 53 54 ≤ 3172832372965 := by decide +kernel

theorem rows22240R_1683 : rowsJ2 76 77 54 55 ≤ 2949516120597 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1674
#print axioms SieveCert.rows22240R_1683
