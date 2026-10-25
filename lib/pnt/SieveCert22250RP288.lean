/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3252–3266 of 5796

File 288 of 465: the parts `rows22250R_3252` … `rows22250R_3266` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99224 tests: row 108 columns 52–53, row 108 columns 54–56, row 108 columns
57–61, row 108 columns 62–69, row 108 columns 70–75, row 108 columns 76–79, row 108 columns 80–81, row 108 columns
82–83, row 108 columns 84–84, row 108 columns 85–85, row 108 columns 86–86, row 108 columns 87–87, row 108 columns
88–88, row 108 columns 89–89, row 108 columns 90–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_3252 : rowsJ2 108 109 52 54 ≤ 2717537461410 := by decide +kernel

theorem rows22250R_3253 : rowsJ2 108 109 54 57 ≤ 1033701776931 := by decide +kernel

theorem rows22250R_3254 : rowsJ2 108 109 57 62 ≤ 0 := by decide +kernel

theorem rows22250R_3255 : rowsJ2 108 109 62 70 ≤ 0 := by decide +kernel

theorem rows22250R_3256 : rowsJ2 108 109 70 76 ≤ 0 := by decide +kernel

theorem rows22250R_3257 : rowsJ2 108 109 76 80 ≤ 0 := by decide +kernel

theorem rows22250R_3258 : rowsJ2 108 109 80 82 ≤ 194431530683 := by decide +kernel

theorem rows22250R_3259 : rowsJ2 108 109 82 84 ≤ 808328396223 := by decide +kernel

theorem rows22250R_3260 : rowsJ2 108 109 84 85 ≤ 765484953327 := by decide +kernel

theorem rows22250R_3261 : rowsJ2 108 109 85 86 ≤ 1070679738343 := by decide +kernel

theorem rows22250R_3262 : rowsJ2 108 109 86 87 ≤ 1435259091158 := by decide +kernel

theorem rows22250R_3263 : rowsJ2 108 109 87 88 ≤ 1315519760056 := by decide +kernel

theorem rows22250R_3264 : rowsJ2 108 109 88 89 ≤ 1206161728065 := by decide +kernel

theorem rows22250R_3265 : rowsJ2 108 109 89 90 ≤ 1127178941975 := by decide +kernel

theorem rows22250R_3266 : rowsJ2 108 109 90 91 ≤ 1126378449046 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3252
#print axioms SieveCert.rows22250R_3266
