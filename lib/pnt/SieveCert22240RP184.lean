/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2089–2100 of 5066

File 184 of 387: the parts `rows22240R_2089` … `rows22240R_2100` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 96696 in units of a depth-4 test: row 85 columns 45–45, row 85 columns
46–46, row 85 columns 47–47, row 85 columns 48–48, row 85 columns 49–49, row 85 columns 50–50, row 85 columns 51–51,
row 85 columns 52–52, row 85 columns 53–53, row 85 columns 54–54, row 85 columns 55–55, row 85 columns 56–56), each
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

theorem rows22240R_2089 : rowsJ2 85 86 45 46 ≤ 3566336451142 := by decide +kernel

theorem rows22240R_2090 : rowsJ2 85 86 46 47 ≤ 110300210544 := by decide +kernel

theorem rows22240R_2091 : rowsJ2 85 86 47 48 ≤ 54860469401 := by decide +kernel

theorem rows22240R_2092 : rowsJ2 85 86 48 49 ≤ 0 := by decide +kernel

theorem rows22240R_2093 : rowsJ2 85 86 49 50 ≤ 0 := by decide +kernel

theorem rows22240R_2094 : rowsJ2 85 86 50 51 ≤ 0 := by decide +kernel

theorem rows22240R_2095 : rowsJ2 85 86 51 52 ≤ 0 := by decide +kernel

theorem rows22240R_2096 : rowsJ2 85 86 52 53 ≤ 0 := by decide +kernel

theorem rows22240R_2097 : rowsJ2 85 86 53 54 ≤ 0 := by decide +kernel

theorem rows22240R_2098 : rowsJ2 85 86 54 55 ≤ 0 := by decide +kernel

theorem rows22240R_2099 : rowsJ2 85 86 55 56 ≤ 0 := by decide +kernel

theorem rows22240R_2100 : rowsJ2 85 86 56 57 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2089
#print axioms SieveCert.rows22240R_2100
