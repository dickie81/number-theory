/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3229–3243 of 4715

File 252 of 351: the parts `rows22250R_3229` … `rows22250R_3243` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 92467 tests: row 121 columns 68–68, row 121 columns 69–69, row 121 columns
70–70, row 121 columns 71–71, row 121 columns 72–73, row 121 columns 74–76, row 121 columns 77–80, row 121 columns
81–84, row 121 columns 85–87, row 121 columns 88–90, row 121 columns 91–92, row 121 columns 93–339, row 122 columns
0–25, row 122 columns 26–28, row 122 columns 29–31), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_3229 : rowsJ2 121 122 68 69 ≤ 3358589123455 := by decide +kernel

theorem rows22250R_3230 : rowsJ2 121 122 69 70 ≤ 3209813559964 := by decide +kernel

theorem rows22250R_3231 : rowsJ2 121 122 70 71 ≤ 2977790834603 := by decide +kernel

theorem rows22250R_3232 : rowsJ2 121 122 71 72 ≤ 2684832879960 := by decide +kernel

theorem rows22250R_3233 : rowsJ2 121 122 72 74 ≤ 3734486445540 := by decide +kernel

theorem rows22250R_3234 : rowsJ2 121 122 74 77 ≤ 1464571295843 := by decide +kernel

theorem rows22250R_3235 : rowsJ2 121 122 77 81 ≤ 0 := by decide +kernel

theorem rows22250R_3236 : rowsJ2 121 122 81 85 ≤ 3003828608864 := by decide +kernel

theorem rows22250R_3237 : rowsJ2 121 122 85 88 ≤ 9472278998344 := by decide +kernel

theorem rows22250R_3238 : rowsJ2 121 122 88 91 ≤ 18767843694146 := by decide +kernel

theorem rows22250R_3239 : rowsJ2 121 122 91 93 ≤ 19180638306472 := by decide +kernel

theorem rows22250R_3240 : rowsJ2 121 122 93 340 ≤ 1223785140318178 := by decide +kernel

theorem rows22250R_3241 : rowsJ2 122 123 0 26 ≤ 3481806412324 := by decide +kernel

theorem rows22250R_3242 : rowsJ2 122 123 26 29 ≤ 14040340508017 := by decide +kernel

theorem rows22250R_3243 : rowsJ2 122 123 29 32 ≤ 17686996788257 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3229
#print axioms SieveCert.rows22250R_3243
