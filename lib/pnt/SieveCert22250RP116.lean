/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1291–1301 of 4715

File 116 of 351: the parts `rows22250R_1291` … `rows22250R_1301` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 95294 tests: row 69 columns 44–44, row 69 columns 45–45, row 69 columns
46–46, row 69 columns 47–47, row 69 columns 48–48, row 69 columns 49–49, row 69 columns 50–50, row 69 columns 51–51,
row 69 columns 52–52, row 69 columns 53–53, row 69 columns 54–54), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1291 : rowsJ2 69 70 44 45 ≤ 63590115754 := by decide +kernel

theorem rows22250R_1292 : rowsJ2 69 70 45 46 ≤ 249591353588 := by decide +kernel

theorem rows22250R_1293 : rowsJ2 69 70 46 47 ≤ 744618034473 := by decide +kernel

theorem rows22250R_1294 : rowsJ2 69 70 47 48 ≤ 1478695914113 := by decide +kernel

theorem rows22250R_1295 : rowsJ2 69 70 48 49 ≤ 2184994599451 := by decide +kernel

theorem rows22250R_1296 : rowsJ2 69 70 49 50 ≤ 2988628260717 := by decide +kernel

theorem rows22250R_1297 : rowsJ2 69 70 50 51 ≤ 3915275696159 := by decide +kernel

theorem rows22250R_1298 : rowsJ2 69 70 51 52 ≤ 4814141630280 := by decide +kernel

theorem rows22250R_1299 : rowsJ2 69 70 52 53 ≤ 5469108525237 := by decide +kernel

theorem rows22250R_1300 : rowsJ2 69 70 53 54 ≤ 5960238962254 := by decide +kernel

theorem rows22250R_1301 : rowsJ2 69 70 54 55 ≤ 6467487265954 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1291
#print axioms SieveCert.rows22250R_1301
