/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3267–3284 of 5796

File 289 of 465: the parts `rows22250R_3267` … `rows22250R_3284` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 97425 tests: row 108 columns 91–91, row 108 columns 92–92, row 108 columns
93–93, row 108 columns 94–94, row 108 columns 95–95, row 108 columns 96–96, row 108 columns 97–97, row 108 columns
98–98, row 108 columns 99–99, row 108 columns 100–100, row 108 columns 101–101, row 108 columns 102–102, row 108
columns 103–103, row 108 columns 104–104, row 108 columns 105–105, row 108 columns 106–106, row 108 columns 107–107,
row 108 columns 108–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3267 : rowsJ2 108 109 91 92 ≤ 1191420186652 := by decide +kernel

theorem rows22250R_3268 : rowsJ2 108 109 92 93 ≤ 1301518425230 := by decide +kernel

theorem rows22250R_3269 : rowsJ2 108 109 93 94 ≤ 1479457841277 := by decide +kernel

theorem rows22250R_3270 : rowsJ2 108 109 94 95 ≤ 1705103180398 := by decide +kernel

theorem rows22250R_3271 : rowsJ2 108 109 95 96 ≤ 2002052853876 := by decide +kernel

theorem rows22250R_3272 : rowsJ2 108 109 96 97 ≤ 2348781384505 := by decide +kernel

theorem rows22250R_3273 : rowsJ2 108 109 97 98 ≤ 2769662281486 := by decide +kernel

theorem rows22250R_3274 : rowsJ2 108 109 98 99 ≤ 3242738637944 := by decide +kernel

theorem rows22250R_3275 : rowsJ2 108 109 99 100 ≤ 3793206279775 := by decide +kernel

theorem rows22250R_3276 : rowsJ2 108 109 100 101 ≤ 4398663444958 := by decide +kernel

theorem rows22250R_3277 : rowsJ2 108 109 101 102 ≤ 5085180131715 := by decide +kernel

theorem rows22250R_3278 : rowsJ2 108 109 102 103 ≤ 5829897640599 := by decide +kernel

theorem rows22250R_3279 : rowsJ2 108 109 103 104 ≤ 6659817249176 := by decide +kernel

theorem rows22250R_3280 : rowsJ2 108 109 104 105 ≤ 7551612980366 := by decide +kernel

theorem rows22250R_3281 : rowsJ2 108 109 105 106 ≤ 8533280483046 := by decide +kernel

theorem rows22250R_3282 : rowsJ2 108 109 106 107 ≤ 9581018412276 := by decide +kernel

theorem rows22250R_3283 : rowsJ2 108 109 107 108 ≤ 10723886745079 := by decide +kernel

theorem rows22250R_3284 : rowsJ2 108 109 108 360 ≤ 11937603574165 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3267
#print axioms SieveCert.rows22250R_3284
