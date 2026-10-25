/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3057–3069 of 5796

File 275 of 465: the parts `rows22250R_3057` … `rows22250R_3069` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 92266 tests: row 104 columns 58–60, row 104 columns 61–65, row 104 columns
66–72, row 104 columns 73–77, row 104 columns 78–80, row 104 columns 81–82, row 104 columns 83–83, row 104 columns
84–84, row 104 columns 85–85, row 104 columns 86–86, row 104 columns 87–87, row 104 columns 88–88, row 104 columns
89–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_3057 : rowsJ2 104 105 58 61 ≤ 68720518519 := by decide +kernel

theorem rows22250R_3058 : rowsJ2 104 105 61 66 ≤ 0 := by decide +kernel

theorem rows22250R_3059 : rowsJ2 104 105 66 73 ≤ 0 := by decide +kernel

theorem rows22250R_3060 : rowsJ2 104 105 73 78 ≤ 0 := by decide +kernel

theorem rows22250R_3061 : rowsJ2 104 105 78 81 ≤ 50025908573 := by decide +kernel

theorem rows22250R_3062 : rowsJ2 104 105 81 83 ≤ 459923323589 := by decide +kernel

theorem rows22250R_3063 : rowsJ2 104 105 83 84 ≤ 519906981572 := by decide +kernel

theorem rows22250R_3064 : rowsJ2 104 105 84 85 ≤ 788208239556 := by decide +kernel

theorem rows22250R_3065 : rowsJ2 104 105 85 86 ≤ 1102808746999 := by decide +kernel

theorem rows22250R_3066 : rowsJ2 104 105 86 87 ≤ 1476879074346 := by decide +kernel

theorem rows22250R_3067 : rowsJ2 104 105 87 88 ≤ 1897854088146 := by decide +kernel

theorem rows22250R_3068 : rowsJ2 104 105 88 89 ≤ 2379204531175 := by decide +kernel

theorem rows22250R_3069 : rowsJ2 104 105 89 90 ≤ 2225575863550 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3057
#print axioms SieveCert.rows22250R_3069
