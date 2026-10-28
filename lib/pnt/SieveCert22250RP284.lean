/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3699–3712 of 4715

File 284 of 351: the parts `rows22250R_3699` … `rows22250R_3712` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 92497 in units of a depth-4 test: row 138 columns 75–77, row 138
columns 78–82, row 138 columns 83–339, row 139 columns 0–23, row 139 columns 24–48, row 139 columns 49–51, row 139
columns 52–53, row 139 columns 54–54, row 139 columns 55–55, row 139 columns 56–56, row 139 columns 57–57, row 139
columns 58–58, row 139 columns 59–59, row 139 columns 60–60), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3699 : rowsJ2 138 139 75 78 ≤ 4878172627463 := by decide +kernel

theorem rows22250R_3700 : rowsJ2 138 139 78 83 ≤ 3281895043669 := by decide +kernel

theorem rows22250R_3701 : rowsJ2 138 139 83 340 ≤ 702081924829893 := by decide +kernel

theorem rows22250R_3702 : rowsJ2 139 140 0 24 ≤ 4594556435722 := by decide +kernel

theorem rows22250R_3703 : rowsJ2 139 140 24 49 ≤ 3672853711629 := by decide +kernel

theorem rows22250R_3704 : rowsJ2 139 140 49 52 ≤ 7095720676337 := by decide +kernel

theorem rows22250R_3705 : rowsJ2 139 140 52 54 ≤ 7781949661197 := by decide +kernel

theorem rows22250R_3706 : rowsJ2 139 140 54 55 ≤ 4958460294496 := by decide +kernel

theorem rows22250R_3707 : rowsJ2 139 140 55 56 ≤ 5732615674286 := by decide +kernel

theorem rows22250R_3708 : rowsJ2 139 140 56 57 ≤ 6551243629747 := by decide +kernel

theorem rows22250R_3709 : rowsJ2 139 140 57 58 ≤ 7412598185036 := by decide +kernel

theorem rows22250R_3710 : rowsJ2 139 140 58 59 ≤ 8315069960121 := by decide +kernel

theorem rows22250R_3711 : rowsJ2 139 140 59 60 ≤ 9257179010559 := by decide +kernel

theorem rows22250R_3712 : rowsJ2 139 140 60 61 ≤ 10216814267644 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3699
#print axioms SieveCert.rows22250R_3712
