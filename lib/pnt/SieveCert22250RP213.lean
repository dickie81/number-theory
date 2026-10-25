/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2275–2284 of 5796

File 213 of 465: the parts `rows22250R_2275` … `rows22250R_2284` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 94629 tests: row 88 columns 49–49, row 88 columns 50–50, row 88 columns
51–51, row 88 columns 52–52, row 88 columns 53–53, row 88 columns 54–54, row 88 columns 55–55, row 88 columns 56–56,
row 88 columns 57–57, row 88 columns 58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2275 : rowsJ2 88 89 49 50 ≤ 362495214958 := by decide +kernel

theorem rows22250R_2276 : rowsJ2 88 89 50 51 ≤ 317758288138 := by decide +kernel

theorem rows22250R_2277 : rowsJ2 88 89 51 52 ≤ 227692181747 := by decide +kernel

theorem rows22250R_2278 : rowsJ2 88 89 52 53 ≤ 182467750655 := by decide +kernel

theorem rows22250R_2279 : rowsJ2 88 89 53 54 ≤ 91301908661 := by decide +kernel

theorem rows22250R_2280 : rowsJ2 88 89 54 55 ≤ 45450874740 := by decide +kernel

theorem rows22250R_2281 : rowsJ2 88 89 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2282 : rowsJ2 88 89 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2283 : rowsJ2 88 89 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2284 : rowsJ2 88 89 58 59 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2275
#print axioms SieveCert.rows22250R_2284
