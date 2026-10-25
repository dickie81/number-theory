/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4271–4282 of 5796

File 354 of 465: the parts `rows22250R_4271` … `rows22250R_4282` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 90717 tests: row 138 columns 29–35, row 138 columns 36–55, row 138 columns
56–58, row 138 columns 59–60, row 138 columns 61–61, row 138 columns 62–62, row 138 columns 63–63, row 138 columns
64–64, row 138 columns 65–65, row 138 columns 66–66, row 138 columns 67–67, row 138 columns 68–68), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4271 : rowsJ2 138 139 29 36 ≤ 5295830178828 := by decide +kernel

theorem rows22250R_4272 : rowsJ2 138 139 36 56 ≤ 2461165914346 := by decide +kernel

theorem rows22250R_4273 : rowsJ2 138 139 56 59 ≤ 4986425946827 := by decide +kernel

theorem rows22250R_4274 : rowsJ2 138 139 59 61 ≤ 5486170045752 := by decide +kernel

theorem rows22250R_4275 : rowsJ2 138 139 61 62 ≤ 3501967763896 := by decide +kernel

theorem rows22250R_4276 : rowsJ2 138 139 62 63 ≤ 4053484704435 := by decide +kernel

theorem rows22250R_4277 : rowsJ2 138 139 63 64 ≤ 4637549990199 := by decide +kernel

theorem rows22250R_4278 : rowsJ2 138 139 64 65 ≤ 5218579084025 := by decide +kernel

theorem rows22250R_4279 : rowsJ2 138 139 65 66 ≤ 5744426472911 := by decide +kernel

theorem rows22250R_4280 : rowsJ2 138 139 66 67 ≤ 6232222708527 := by decide +kernel

theorem rows22250R_4281 : rowsJ2 138 139 67 68 ≤ 6664178656939 := by decide +kernel

theorem rows22250R_4282 : rowsJ2 138 139 68 69 ≤ 7057413368011 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4271
#print axioms SieveCert.rows22250R_4282
