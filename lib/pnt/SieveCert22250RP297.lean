/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3401–3417 of 5796

File 297 of 465: the parts `rows22250R_3401` … `rows22250R_3417` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 98680 tests: row 111 columns 59–67, row 111 columns 68–73, row 111 columns
74–77, row 111 columns 78–80, row 111 columns 81–82, row 111 columns 83–83, row 111 columns 84–84, row 111 columns
85–85, row 111 columns 86–86, row 111 columns 87–87, row 111 columns 88–88, row 111 columns 89–89, row 111 columns
90–90, row 111 columns 91–92, row 111 columns 93–94, row 111 columns 95–96, row 111 columns 97–97), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3401 : rowsJ2 111 112 59 68 ≤ 0 := by decide +kernel

theorem rows22250R_3402 : rowsJ2 111 112 68 74 ≤ 0 := by decide +kernel

theorem rows22250R_3403 : rowsJ2 111 112 74 78 ≤ 0 := by decide +kernel

theorem rows22250R_3404 : rowsJ2 111 112 78 81 ≤ 47848146777 := by decide +kernel

theorem rows22250R_3405 : rowsJ2 111 112 81 83 ≤ 438824393277 := by decide +kernel

theorem rows22250R_3406 : rowsJ2 111 112 83 84 ≤ 494400453406 := by decide +kernel

theorem rows22250R_3407 : rowsJ2 111 112 84 85 ≤ 748700931286 := by decide +kernel

theorem rows22250R_3408 : rowsJ2 111 112 85 86 ≤ 844060904242 := by decide +kernel

theorem rows22250R_3409 : rowsJ2 111 112 86 87 ≤ 756877784058 := by decide +kernel

theorem rows22250R_3410 : rowsJ2 111 112 87 88 ≤ 668692350185 := by decide +kernel

theorem rows22250R_3411 : rowsJ2 111 112 88 89 ≤ 659580286116 := by decide +kernel

theorem rows22250R_3412 : rowsJ2 111 112 89 90 ≤ 683205605806 := by decide +kernel

theorem rows22250R_3413 : rowsJ2 111 112 90 91 ≤ 787875899517 := by decide +kernel

theorem rows22250R_3414 : rowsJ2 111 112 91 93 ≤ 2079603281458 := by decide +kernel

theorem rows22250R_3415 : rowsJ2 111 112 93 95 ≤ 3174764067882 := by decide +kernel

theorem rows22250R_3416 : rowsJ2 111 112 95 97 ≤ 4776467555083 := by decide +kernel

theorem rows22250R_3417 : rowsJ2 111 112 97 98 ≤ 3146915333837 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3401
#print axioms SieveCert.rows22250R_3417
