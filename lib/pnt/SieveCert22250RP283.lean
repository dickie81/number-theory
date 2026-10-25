/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3686–3698 of 4715

File 283 of 351: the parts `rows22250R_3686` … `rows22250R_3698` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 99525 tests: row 138 columns 61–61, row 138 columns 62–62, row 138 columns
63–63, row 138 columns 64–64, row 138 columns 65–65, row 138 columns 66–66, row 138 columns 67–67, row 138 columns
68–68, row 138 columns 69–69, row 138 columns 70–70, row 138 columns 71–71, row 138 columns 72–72, row 138 columns
73–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3686 : rowsJ2 138 139 61 62 ≤ 10443751710808 := by decide +kernel

theorem rows22250R_3687 : rowsJ2 138 139 62 63 ≤ 11257734298303 := by decide +kernel

theorem rows22250R_3688 : rowsJ2 138 139 63 64 ≤ 12025949569313 := by decide +kernel

theorem rows22250R_3689 : rowsJ2 138 139 64 65 ≤ 10860767261124 := by decide +kernel

theorem rows22250R_3690 : rowsJ2 138 139 65 66 ≤ 9772481205979 := by decide +kernel

theorem rows22250R_3691 : rowsJ2 138 139 66 67 ≤ 8737557955855 := by decide +kernel

theorem rows22250R_3692 : rowsJ2 138 139 67 68 ≤ 7775584884092 := by decide +kernel

theorem rows22250R_3693 : rowsJ2 138 139 68 69 ≤ 6863012034338 := by decide +kernel

theorem rows22250R_3694 : rowsJ2 138 139 69 70 ≤ 6019882332964 := by decide +kernel

theorem rows22250R_3695 : rowsJ2 138 139 70 71 ≤ 5222590851414 := by decide +kernel

theorem rows22250R_3696 : rowsJ2 138 139 71 72 ≤ 4491630564398 := by decide +kernel

theorem rows22250R_3697 : rowsJ2 138 139 72 73 ≤ 3803305856585 := by decide +kernel

theorem rows22250R_3698 : rowsJ2 138 139 73 75 ≤ 5772123324657 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3686
#print axioms SieveCert.rows22250R_3698
