/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4188–4201 of 5796

File 348 of 465: the parts `rows22250R_4188` … `rows22250R_4201` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 95144 tests: row 135 columns 71–71, row 135 columns 72–72, row 135 columns
73–73, row 135 columns 74–74, row 135 columns 75–75, row 135 columns 76–76, row 135 columns 77–77, row 135 columns
78–78, row 135 columns 79–79, row 135 columns 80–80, row 135 columns 81–82, row 135 columns 83–84, row 135 columns
85–87, row 135 columns 88–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_4188 : rowsJ2 135 136 71 72 ≤ 6322324319882 := by decide +kernel

theorem rows22250R_4189 : rowsJ2 135 136 72 73 ≤ 6442321123363 := by decide +kernel

theorem rows22250R_4190 : rowsJ2 135 136 73 74 ≤ 6114688444004 := by decide +kernel

theorem rows22250R_4191 : rowsJ2 135 136 74 75 ≤ 5430946478047 := by decide +kernel

theorem rows22250R_4192 : rowsJ2 135 136 75 76 ≤ 4782321418439 := by decide +kernel

theorem rows22250R_4193 : rowsJ2 135 136 76 77 ≤ 4186251785445 := by decide +kernel

theorem rows22250R_4194 : rowsJ2 135 136 77 78 ≤ 3622920952013 := by decide +kernel

theorem rows22250R_4195 : rowsJ2 135 136 78 79 ≤ 3110108946045 := by decide +kernel

theorem rows22250R_4196 : rowsJ2 135 136 79 80 ≤ 2627880785982 := by decide +kernel

theorem rows22250R_4197 : rowsJ2 135 136 80 81 ≤ 2194359995996 := by decide +kernel

theorem rows22250R_4198 : rowsJ2 135 136 81 83 ≤ 3221154546533 := by decide +kernel

theorem rows22250R_4199 : rowsJ2 135 136 83 85 ≤ 1916285607983 := by decide +kernel

theorem rows22250R_4200 : rowsJ2 135 136 85 88 ≤ 1648189668354 := by decide +kernel

theorem rows22250R_4201 : rowsJ2 135 136 88 91 ≤ 6422691726286 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4188
#print axioms SieveCert.rows22250R_4201
