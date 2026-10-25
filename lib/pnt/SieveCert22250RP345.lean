/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4145–4158 of 5796

File 345 of 465: the parts `rows22250R_4145` … `rows22250R_4158` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 99193 tests: row 134 columns 57–59, row 134 columns 60–61, row 134 columns
62–62, row 134 columns 63–63, row 134 columns 64–64, row 134 columns 65–65, row 134 columns 66–66, row 134 columns
67–67, row 134 columns 68–68, row 134 columns 69–69, row 134 columns 70–70, row 134 columns 71–71, row 134 columns
72–72, row 134 columns 73–73), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4145 : rowsJ2 134 135 57 60 ≤ 3674561549931 := by decide +kernel

theorem rows22250R_4146 : rowsJ2 134 135 60 62 ≤ 4312430850029 := by decide +kernel

theorem rows22250R_4147 : rowsJ2 134 135 62 63 ≤ 2824467775462 := by decide +kernel

theorem rows22250R_4148 : rowsJ2 134 135 63 64 ≤ 3315166729579 := by decide +kernel

theorem rows22250R_4149 : rowsJ2 134 135 64 65 ≤ 3802986347257 := by decide +kernel

theorem rows22250R_4150 : rowsJ2 134 135 65 66 ≤ 4234577102768 := by decide +kernel

theorem rows22250R_4151 : rowsJ2 134 135 66 67 ≤ 4627372947682 := by decide +kernel

theorem rows22250R_4152 : rowsJ2 134 135 67 68 ≤ 4963127804953 := by decide +kernel

theorem rows22250R_4153 : rowsJ2 134 135 68 69 ≤ 5259262943835 := by decide +kernel

theorem rows22250R_4154 : rowsJ2 134 135 69 70 ≤ 5497172546917 := by decide +kernel

theorem rows22250R_4155 : rowsJ2 134 135 70 71 ≤ 5694259413794 := by decide +kernel

theorem rows22250R_4156 : rowsJ2 134 135 71 72 ≤ 5831527184528 := by decide +kernel

theorem rows22250R_4157 : rowsJ2 134 135 72 73 ≤ 5926349541574 := by decide +kernel

theorem rows22250R_4158 : rowsJ2 134 135 73 74 ≤ 5959302956684 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4145
#print axioms SieveCert.rows22250R_4158
