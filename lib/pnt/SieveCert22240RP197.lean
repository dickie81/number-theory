/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2268–2282 of 5066

File 197 of 387: the parts `rows22240R_2268` … `rows22240R_2282` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 99796 in units of a depth-4 test: row 89 columns 44–44, row 89 columns
45–45, row 89 columns 46–46, row 89 columns 47–47, row 89 columns 48–48, row 89 columns 49–49, row 89 columns 50–50,
row 89 columns 51–51, row 89 columns 52–52, row 89 columns 53–53, row 89 columns 54–54, row 89 columns 55–55, row 89
columns 56–56, row 89 columns 57–57, row 89 columns 58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_2268 : rowsJ2 89 90 44 45 ≤ 13977967834371 := by decide +kernel

theorem rows22240R_2269 : rowsJ2 89 90 45 46 ≤ 15241935173008 := by decide +kernel

theorem rows22240R_2270 : rowsJ2 89 90 46 47 ≤ 16329672036051 := by decide +kernel

theorem rows22240R_2271 : rowsJ2 89 90 47 48 ≤ 12184772564778 := by decide +kernel

theorem rows22240R_2272 : rowsJ2 89 90 48 49 ≤ 7466157168175 := by decide +kernel

theorem rows22240R_2273 : rowsJ2 89 90 49 50 ≤ 3226653207793 := by decide +kernel

theorem rows22240R_2274 : rowsJ2 89 90 50 51 ≤ 0 := by decide +kernel

theorem rows22240R_2275 : rowsJ2 89 90 51 52 ≤ 0 := by decide +kernel

theorem rows22240R_2276 : rowsJ2 89 90 52 53 ≤ 0 := by decide +kernel

theorem rows22240R_2277 : rowsJ2 89 90 53 54 ≤ 0 := by decide +kernel

theorem rows22240R_2278 : rowsJ2 89 90 54 55 ≤ 0 := by decide +kernel

theorem rows22240R_2279 : rowsJ2 89 90 55 56 ≤ 0 := by decide +kernel

theorem rows22240R_2280 : rowsJ2 89 90 56 57 ≤ 0 := by decide +kernel

theorem rows22240R_2281 : rowsJ2 89 90 57 58 ≤ 0 := by decide +kernel

theorem rows22240R_2282 : rowsJ2 89 90 58 59 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2268
#print axioms SieveCert.rows22240R_2282
