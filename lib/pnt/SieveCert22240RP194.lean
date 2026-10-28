/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2228–2242 of 5066

File 194 of 387: the parts `rows22240R_2228` … `rows22240R_2242` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 94710 in units of a depth-4 test: row 88 columns 49–49, row 88 columns
50–50, row 88 columns 51–51, row 88 columns 52–52, row 88 columns 53–53, row 88 columns 54–54, row 88 columns 55–55,
row 88 columns 56–56, row 88 columns 57–57, row 88 columns 58–58, row 88 columns 59–59, row 88 columns 60–61, row 88
columns 62–63, row 88 columns 64–65, row 88 columns 66–68), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_2228 : rowsJ2 88 89 49 50 ≤ 0 := by decide +kernel

theorem rows22240R_2229 : rowsJ2 88 89 50 51 ≤ 0 := by decide +kernel

theorem rows22240R_2230 : rowsJ2 88 89 51 52 ≤ 0 := by decide +kernel

theorem rows22240R_2231 : rowsJ2 88 89 52 53 ≤ 0 := by decide +kernel

theorem rows22240R_2232 : rowsJ2 88 89 53 54 ≤ 0 := by decide +kernel

theorem rows22240R_2233 : rowsJ2 88 89 54 55 ≤ 0 := by decide +kernel

theorem rows22240R_2234 : rowsJ2 88 89 55 56 ≤ 0 := by decide +kernel

theorem rows22240R_2235 : rowsJ2 88 89 56 57 ≤ 0 := by decide +kernel

theorem rows22240R_2236 : rowsJ2 88 89 57 58 ≤ 0 := by decide +kernel

theorem rows22240R_2237 : rowsJ2 88 89 58 59 ≤ 0 := by decide +kernel

theorem rows22240R_2238 : rowsJ2 88 89 59 60 ≤ 0 := by decide +kernel

theorem rows22240R_2239 : rowsJ2 88 89 60 62 ≤ 0 := by decide +kernel

theorem rows22240R_2240 : rowsJ2 88 89 62 64 ≤ 0 := by decide +kernel

theorem rows22240R_2241 : rowsJ2 88 89 64 66 ≤ 0 := by decide +kernel

theorem rows22240R_2242 : rowsJ2 88 89 66 69 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2228
#print axioms SieveCert.rows22240R_2242
