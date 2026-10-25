/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2240–2256 of 4715

File 186 of 351: the parts `rows22250R_2240` … `rows22250R_2256` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 98633 tests: row 91 columns 48–48, row 91 columns 49–49, row 91 columns
50–50, row 91 columns 51–51, row 91 columns 52–52, row 91 columns 53–53, row 91 columns 54–55, row 91 columns 56–57,
row 91 columns 58–59, row 91 columns 60–62, row 91 columns 63–67, row 91 columns 68–72, row 91 columns 73–76, row 91
columns 77–78, row 91 columns 79–79, row 91 columns 80–80, row 91 columns 81–81), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2240 : rowsJ2 91 92 48 49 ≤ 7787511669183 := by decide +kernel

theorem rows22250R_2241 : rowsJ2 91 92 49 50 ≤ 4469067344433 := by decide +kernel

theorem rows22250R_2242 : rowsJ2 91 92 50 51 ≤ 2070340269947 := by decide +kernel

theorem rows22250R_2243 : rowsJ2 91 92 51 52 ≤ 0 := by decide +kernel

theorem rows22250R_2244 : rowsJ2 91 92 52 53 ≤ 0 := by decide +kernel

theorem rows22250R_2245 : rowsJ2 91 92 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2246 : rowsJ2 91 92 54 56 ≤ 0 := by decide +kernel

theorem rows22250R_2247 : rowsJ2 91 92 56 58 ≤ 0 := by decide +kernel

theorem rows22250R_2248 : rowsJ2 91 92 58 60 ≤ 0 := by decide +kernel

theorem rows22250R_2249 : rowsJ2 91 92 60 63 ≤ 0 := by decide +kernel

theorem rows22250R_2250 : rowsJ2 91 92 63 68 ≤ 0 := by decide +kernel

theorem rows22250R_2251 : rowsJ2 91 92 68 73 ≤ 0 := by decide +kernel

theorem rows22250R_2252 : rowsJ2 91 92 73 77 ≤ 115354324833 := by decide +kernel

theorem rows22250R_2253 : rowsJ2 91 92 77 79 ≤ 753283332003 := by decide +kernel

theorem rows22250R_2254 : rowsJ2 91 92 79 80 ≤ 799185786127 := by decide +kernel

theorem rows22250R_2255 : rowsJ2 91 92 80 81 ≤ 1170961793747 := by decide +kernel

theorem rows22250R_2256 : rowsJ2 91 92 81 82 ≤ 1618921179349 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2240
#print axioms SieveCert.rows22250R_2256
