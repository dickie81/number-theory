/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3291–3306 of 4715

File 256 of 351: the parts `rows22250R_3291` … `rows22250R_3306` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99083 tests: row 123 columns 91–339, row 124 columns 0–25, row 124 columns
26–28, row 124 columns 29–32, row 124 columns 33–41, row 124 columns 42–56, row 124 columns 57–58, row 124 columns
59–60, row 124 columns 61–61, row 124 columns 62–62, row 124 columns 63–63, row 124 columns 64–64, row 124 columns
65–65, row 124 columns 66–66, row 124 columns 67–67, row 124 columns 68–68), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3291 : rowsJ2 123 124 91 340 ≤ 1123666745906154 := by decide +kernel

theorem rows22250R_3292 : rowsJ2 124 125 0 26 ≤ 5025236698812 := by decide +kernel

theorem rows22250R_3293 : rowsJ2 124 125 26 29 ≤ 15188748200993 := by decide +kernel

theorem rows22250R_3294 : rowsJ2 124 125 29 33 ≤ 15853276662887 := by decide +kernel

theorem rows22250R_3295 : rowsJ2 124 125 33 42 ≤ 7751758582193 := by decide +kernel

theorem rows22250R_3296 : rowsJ2 124 125 42 57 ≤ 3415645206189 := by decide +kernel

theorem rows22250R_3297 : rowsJ2 124 125 57 59 ≤ 3735692222942 := by decide +kernel

theorem rows22250R_3298 : rowsJ2 124 125 59 61 ≤ 5644044527296 := by decide +kernel

theorem rows22250R_3299 : rowsJ2 124 125 61 62 ≤ 3527350998663 := by decide +kernel

theorem rows22250R_3300 : rowsJ2 124 125 62 63 ≤ 3909021706440 := by decide +kernel

theorem rows22250R_3301 : rowsJ2 124 125 63 64 ≤ 4240727959170 := by decide +kernel

theorem rows22250R_3302 : rowsJ2 124 125 64 65 ≤ 4498782818149 := by decide +kernel

theorem rows22250R_3303 : rowsJ2 124 125 65 66 ≤ 4705398665679 := by decide +kernel

theorem rows22250R_3304 : rowsJ2 124 125 66 67 ≤ 4836364708213 := by decide +kernel

theorem rows22250R_3305 : rowsJ2 124 125 67 68 ≤ 4913843811136 := by decide +kernel

theorem rows22250R_3306 : rowsJ2 124 125 68 69 ≤ 4913050517572 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3291
#print axioms SieveCert.rows22250R_3306
