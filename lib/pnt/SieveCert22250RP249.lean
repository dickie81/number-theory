/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3182–3196 of 4715

File 249 of 351: the parts `rows22250R_3182` … `rows22250R_3196` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99374 tests: row 119 columns 70–71, row 119 columns 72–74, row 119 columns
75–78, row 119 columns 79–82, row 119 columns 83–85, row 119 columns 86–88, row 119 columns 89–90, row 119 columns
91–92, row 119 columns 93–107, row 119 columns 108–339, row 120 columns 0–25, row 120 columns 26–28, row 120 columns
29–31, row 120 columns 32–35, row 120 columns 36–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_3182 : rowsJ2 119 120 70 72 ≤ 3470025962714 := by decide +kernel

theorem rows22250R_3183 : rowsJ2 119 120 72 75 ≤ 1685279351550 := by decide +kernel

theorem rows22250R_3184 : rowsJ2 119 120 75 79 ≤ 0 := by decide +kernel

theorem rows22250R_3185 : rowsJ2 119 120 79 83 ≤ 377995230144 := by decide +kernel

theorem rows22250R_3186 : rowsJ2 119 120 83 86 ≤ 4184779417776 := by decide +kernel

theorem rows22250R_3187 : rowsJ2 119 120 86 89 ≤ 10779740502128 := by decide +kernel

theorem rows22250R_3188 : rowsJ2 119 120 89 91 ≤ 12173400571690 := by decide +kernel

theorem rows22250R_3189 : rowsJ2 119 120 91 93 ≤ 17181135524494 := by decide +kernel

theorem rows22250R_3190 : rowsJ2 119 120 93 108 ≤ 1259595094391193 := by decide +kernel

theorem rows22250R_3191 : rowsJ2 119 120 108 340 ≤ 88136293744371 := by decide +kernel

theorem rows22250R_3192 : rowsJ2 120 121 0 26 ≤ 1958820570236 := by decide +kernel

theorem rows22250R_3193 : rowsJ2 120 121 26 29 ≤ 11715429330381 := by decide +kernel

theorem rows22250R_3194 : rowsJ2 120 121 29 32 ≤ 21885673785142 := by decide +kernel

theorem rows22250R_3195 : rowsJ2 120 121 32 36 ≤ 18297825890420 := by decide +kernel

theorem rows22250R_3196 : rowsJ2 120 121 36 43 ≤ 7725245678206 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3182
#print axioms SieveCert.rows22250R_3196
