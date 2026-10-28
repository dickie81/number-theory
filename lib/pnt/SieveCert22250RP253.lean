/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3244–3260 of 4715

File 253 of 351: the parts `rows22250R_3244` … `rows22250R_3260` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 94572 in units of a depth-4 test: row 122 columns 32–36, row 122
columns 37–53, row 122 columns 54–58, row 122 columns 59–60, row 122 columns 61–61, row 122 columns 62–62, row 122
columns 63–63, row 122 columns 64–64, row 122 columns 65–65, row 122 columns 66–66, row 122 columns 67–67, row 122
columns 68–68, row 122 columns 69–69, row 122 columns 70–70, row 122 columns 71–71, row 122 columns 72–73, row 122
columns 74–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3244 : rowsJ2 122 123 32 37 ≤ 14933521032177 := by decide +kernel

theorem rows22250R_3245 : rowsJ2 122 123 37 54 ≤ 2692708054220 := by decide +kernel

theorem rows22250R_3246 : rowsJ2 122 123 54 59 ≤ 4674148070377 := by decide +kernel

theorem rows22250R_3247 : rowsJ2 122 123 59 61 ≤ 4507331415439 := by decide +kernel

theorem rows22250R_3248 : rowsJ2 122 123 61 62 ≤ 2875422447540 := by decide +kernel

theorem rows22250R_3249 : rowsJ2 122 123 62 63 ≤ 3200613436495 := by decide +kernel

theorem rows22250R_3250 : rowsJ2 122 123 63 64 ≤ 3475408348002 := by decide +kernel

theorem rows22250R_3251 : rowsJ2 122 123 64 65 ≤ 3675798059525 := by decide +kernel

theorem rows22250R_3252 : rowsJ2 122 123 65 66 ≤ 3824215766727 := by decide +kernel

theorem rows22250R_3253 : rowsJ2 122 123 66 67 ≤ 3896122025237 := by decide +kernel

theorem rows22250R_3254 : rowsJ2 122 123 67 68 ≤ 3913899466751 := by decide +kernel

theorem rows22250R_3255 : rowsJ2 122 123 68 69 ≤ 3852426526266 := by decide +kernel

theorem rows22250R_3256 : rowsJ2 122 123 69 70 ≤ 3734012175197 := by decide +kernel

theorem rows22250R_3257 : rowsJ2 122 123 70 71 ≤ 3532890237240 := by decide +kernel

theorem rows22250R_3258 : rowsJ2 122 123 71 72 ≤ 3271261670876 := by decide +kernel

theorem rows22250R_3259 : rowsJ2 122 123 72 74 ≤ 4576954482379 := by decide +kernel

theorem rows22250R_3260 : rowsJ2 122 123 74 76 ≤ 2303000023807 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3244
#print axioms SieveCert.rows22250R_3260
