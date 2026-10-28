/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3275–3290 of 4715

File 255 of 351: the parts `rows22250R_3275` … `rows22250R_3290` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 93940 in units of a depth-4 test: row 123 columns 63–63, row 123
columns 64–64, row 123 columns 65–65, row 123 columns 66–66, row 123 columns 67–67, row 123 columns 68–68, row 123
columns 69–69, row 123 columns 70–70, row 123 columns 71–71, row 123 columns 72–72, row 123 columns 73–74, row 123
columns 75–77, row 123 columns 78–81, row 123 columns 82–85, row 123 columns 86–88, row 123 columns 89–90), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3275 : rowsJ2 123 124 63 64 ≤ 3855874524294 := by decide +kernel

theorem rows22250R_3276 : rowsJ2 123 124 64 65 ≤ 4084906200902 := by decide +kernel

theorem rows22250R_3277 : rowsJ2 123 124 65 66 ≤ 4262229619213 := by decide +kernel

theorem rows22250R_3278 : rowsJ2 123 124 66 67 ≤ 4363470241176 := by decide +kernel

theorem rows22250R_3279 : rowsJ2 123 124 67 68 ≤ 4410899768184 := by decide +kernel

theorem rows22250R_3280 : rowsJ2 123 124 68 69 ≤ 4379565259827 := by decide +kernel

theorem rows22250R_3281 : rowsJ2 123 124 69 70 ≤ 4291665582508 := by decide +kernel

theorem rows22250R_3282 : rowsJ2 123 124 70 71 ≤ 4121607468232 := by decide +kernel

theorem rows22250R_3283 : rowsJ2 123 124 71 72 ≤ 3663031953255 := by decide +kernel

theorem rows22250R_3284 : rowsJ2 123 124 72 73 ≤ 2985371794911 := by decide +kernel

theorem rows22250R_3285 : rowsJ2 123 124 73 75 ≤ 4168133201097 := by decide +kernel

theorem rows22250R_3286 : rowsJ2 123 124 75 78 ≤ 2472524910495 := by decide +kernel

theorem rows22250R_3287 : rowsJ2 123 124 78 82 ≤ 0 := by decide +kernel

theorem rows22250R_3288 : rowsJ2 123 124 82 86 ≤ 6100898311120 := by decide +kernel

theorem rows22250R_3289 : rowsJ2 123 124 86 89 ≤ 13847596703959 := by decide +kernel

theorem rows22250R_3290 : rowsJ2 123 124 89 91 ≤ 15318188552345 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3275
#print axioms SieveCert.rows22250R_3290
