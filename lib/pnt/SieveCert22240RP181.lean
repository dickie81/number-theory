/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2046–2057 of 5066

File 181 of 387: the parts `rows22240R_2046` … `rows22240R_2057` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 96945 in units of a depth-4 test: row 84 columns 47–47, row 84 columns
48–48, row 84 columns 49–49, row 84 columns 50–50, row 84 columns 51–51, row 84 columns 52–52, row 84 columns 53–53,
row 84 columns 54–54, row 84 columns 55–55, row 84 columns 56–56, row 84 columns 57–57, row 84 columns 58–58), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_2046 : rowsJ2 84 85 47 48 ≤ 221209191960 := by decide +kernel

theorem rows22240R_2047 : rowsJ2 84 85 48 49 ≤ 279930639619 := by decide +kernel

theorem rows22240R_2048 : rowsJ2 84 85 49 50 ≤ 225298221397 := by decide +kernel

theorem rows22240R_2049 : rowsJ2 84 85 50 51 ≤ 225413309301 := by decide +kernel

theorem rows22240R_2050 : rowsJ2 84 85 51 52 ≤ 170151560823 := by decide +kernel

theorem rows22240R_2051 : rowsJ2 84 85 52 53 ≤ 170305511226 := by decide +kernel

theorem rows22240R_2052 : rowsJ2 84 85 53 54 ≤ 114316453484 := by decide +kernel

theorem rows22240R_2053 : rowsJ2 84 85 54 55 ≤ 114464668920 := by decide +kernel

theorem rows22240R_2054 : rowsJ2 84 85 55 56 ≤ 57648454284 := by decide +kernel

theorem rows22240R_2055 : rowsJ2 84 85 56 57 ≤ 57745701807 := by decide +kernel

theorem rows22240R_2056 : rowsJ2 84 85 57 58 ≤ 0 := by decide +kernel

theorem rows22240R_2057 : rowsJ2 84 85 58 59 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2046
#print axioms SieveCert.rows22240R_2057
