/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1206–1213 of 4715

File 109 of 351: the parts `rows22250R_1206` … `rows22250R_1213` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 87906 tests: row 67 columns 49–49, row 67 columns 50–50, row 67 columns
51–51, row 67 columns 52–52, row 67 columns 53–53, row 67 columns 54–54, row 67 columns 55–55, row 67 columns
56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1206 : rowsJ2 67 68 49 50 ≤ 3041045554512 := by decide +kernel

theorem rows22250R_1207 : rowsJ2 67 68 50 51 ≤ 4085245397406 := by decide +kernel

theorem rows22250R_1208 : rowsJ2 67 68 51 52 ≤ 5155621573792 := by decide +kernel

theorem rows22250R_1209 : rowsJ2 67 68 52 53 ≤ 5981413614063 := by decide +kernel

theorem rows22250R_1210 : rowsJ2 67 68 53 54 ≤ 6646034221585 := by decide +kernel

theorem rows22250R_1211 : rowsJ2 67 68 54 55 ≤ 7331379584440 := by decide +kernel

theorem rows22250R_1212 : rowsJ2 67 68 55 56 ≤ 7987232164619 := by decide +kernel

theorem rows22250R_1213 : rowsJ2 67 68 56 57 ≤ 8454947539155 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1206
#print axioms SieveCert.rows22250R_1213
