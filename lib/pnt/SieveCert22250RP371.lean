/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4486–4500 of 5796

File 371 of 465: the parts `rows22250R_4486` … `rows22250R_4500` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 96151 tests: row 144 columns 76–76, row 144 columns 77–77, row 144 columns
78–78, row 144 columns 79–79, row 144 columns 80–81, row 144 columns 82–84, row 144 columns 85–88, row 144 columns
89–359, row 145 columns 0–23, row 145 columns 24–35, row 145 columns 36–53, row 145 columns 54–55, row 145 columns
56–57, row 145 columns 58–58, row 145 columns 59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4486 : rowsJ2 144 145 76 77 ≤ 4197505800863 := by decide +kernel

theorem rows22250R_4487 : rowsJ2 144 145 77 78 ≤ 3629500185568 := by decide +kernel

theorem rows22250R_4488 : rowsJ2 144 145 78 79 ≤ 3111799742761 := by decide +kernel

theorem rows22250R_4489 : rowsJ2 144 145 79 80 ≤ 2625357508027 := by decide +kernel

theorem rows22250R_4490 : rowsJ2 144 145 80 82 ≤ 3966233140937 := by decide +kernel

theorem rows22250R_4491 : rowsJ2 144 145 82 85 ≤ 3294543101870 := by decide +kernel

theorem rows22250R_4492 : rowsJ2 144 145 85 89 ≤ 4356669567046 := by decide +kernel

theorem rows22250R_4493 : rowsJ2 144 145 89 360 ≤ 408080893447450 := by decide +kernel

theorem rows22250R_4494 : rowsJ2 145 146 0 24 ≤ 2779125962656 := by decide +kernel

theorem rows22250R_4495 : rowsJ2 145 146 24 36 ≤ 2507181885125 := by decide +kernel

theorem rows22250R_4496 : rowsJ2 145 146 36 54 ≤ 4948565265387 := by decide +kernel

theorem rows22250R_4497 : rowsJ2 145 146 54 56 ≤ 4549337334472 := by decide +kernel

theorem rows22250R_4498 : rowsJ2 145 146 56 58 ≤ 6598388085073 := by decide +kernel

theorem rows22250R_4499 : rowsJ2 145 146 58 59 ≤ 4165107378284 := by decide +kernel

theorem rows22250R_4500 : rowsJ2 145 146 59 60 ≤ 4791247089364 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4486
#print axioms SieveCert.rows22250R_4500
