/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3301–3315 of 5796

File 291 of 465: the parts `rows22250R_3301` … `rows22250R_3315` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 96568 tests: row 109 columns 51–52, row 109 columns 53–55, row 109 columns
56–60, row 109 columns 61–68, row 109 columns 69–74, row 109 columns 75–78, row 109 columns 79–81, row 109 columns
82–83, row 109 columns 84–84, row 109 columns 85–85, row 109 columns 86–86, row 109 columns 87–87, row 109 columns
88–88, row 109 columns 89–89, row 109 columns 90–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3301 : rowsJ2 109 110 51 53 ≤ 3043881386857 := by decide +kernel

theorem rows22250R_3302 : rowsJ2 109 110 53 56 ≤ 1423801787251 := by decide +kernel

theorem rows22250R_3303 : rowsJ2 109 110 56 61 ≤ 0 := by decide +kernel

theorem rows22250R_3304 : rowsJ2 109 110 61 69 ≤ 0 := by decide +kernel

theorem rows22250R_3305 : rowsJ2 109 110 69 75 ≤ 0 := by decide +kernel

theorem rows22250R_3306 : rowsJ2 109 110 75 79 ≤ 0 := by decide +kernel

theorem rows22250R_3307 : rowsJ2 109 110 79 82 ≤ 193207141077 := by decide +kernel

theorem rows22250R_3308 : rowsJ2 109 110 82 84 ≤ 802201918354 := by decide +kernel

theorem rows22250R_3309 : rowsJ2 109 110 84 85 ≤ 759781202363 := by decide +kernel

theorem rows22250R_3310 : rowsJ2 109 110 85 86 ≤ 1063293371242 := by decide +kernel

theorem rows22250R_3311 : rowsJ2 109 110 86 87 ≤ 1184774090535 := by decide +kernel

theorem rows22250R_3312 : rowsJ2 109 110 87 88 ≤ 1075191513275 := by decide +kernel

theorem rows22250R_3313 : rowsJ2 109 110 88 89 ≤ 975973165006 := by decide +kernel

theorem rows22250R_3314 : rowsJ2 109 110 89 90 ≤ 942399886483 := by decide +kernel

theorem rows22250R_3315 : rowsJ2 109 110 90 91 ≤ 987637797065 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3301
#print axioms SieveCert.rows22250R_3315
