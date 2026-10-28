/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3261–3274 of 4715

File 254 of 351: the parts `rows22250R_3261` … `rows22250R_3274` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 98807 in units of a depth-4 test: row 122 columns 76–79, row 122
columns 80–83, row 122 columns 84–86, row 122 columns 87–89, row 122 columns 90–91, row 122 columns 92–339, row 123
columns 0–25, row 123 columns 26–28, row 123 columns 29–32, row 123 columns 33–39, row 123 columns 40–56, row 123
columns 57–59, row 123 columns 60–61, row 123 columns 62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3261 : rowsJ2 122 123 76 80 ≤ 417837122619 := by decide +kernel

theorem rows22250R_3262 : rowsJ2 122 123 80 84 ≤ 1494499583772 := by decide +kernel

theorem rows22250R_3263 : rowsJ2 122 123 84 87 ≤ 7462199771812 := by decide +kernel

theorem rows22250R_3264 : rowsJ2 122 123 87 90 ≤ 16249386773939 := by decide +kernel

theorem rows22250R_3265 : rowsJ2 122 123 90 92 ≤ 17212979039973 := by decide +kernel

theorem rows22250R_3266 : rowsJ2 122 123 92 340 ≤ 1130412708648130 := by decide +kernel

theorem rows22250R_3267 : rowsJ2 123 124 0 26 ≤ 4251342109710 := by decide +kernel

theorem rows22250R_3268 : rowsJ2 123 124 26 29 ≤ 15270394949481 := by decide +kernel

theorem rows22250R_3269 : rowsJ2 123 124 29 33 ≤ 18672533144274 := by decide +kernel

theorem rows22250R_3270 : rowsJ2 123 124 33 40 ≤ 10401826566491 := by decide +kernel

theorem rows22250R_3271 : rowsJ2 123 124 40 57 ≤ 2754448596363 := by decide +kernel

theorem rows22250R_3272 : rowsJ2 123 124 57 60 ≤ 5575975119739 := by decide +kernel

theorem rows22250R_3273 : rowsJ2 123 124 60 62 ≤ 5973352294739 := by decide +kernel

theorem rows22250R_3274 : rowsJ2 123 124 62 63 ≤ 3552812821141 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3261
#print axioms SieveCert.rows22250R_3274
