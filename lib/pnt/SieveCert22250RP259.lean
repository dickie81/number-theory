/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3337–3350 of 4715

File 259 of 351: the parts `rows22250R_3337` … `rows22250R_3350` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 96519 tests: row 125 columns 73–73, row 125 columns 74–75, row 125 columns
76–78, row 125 columns 79–82, row 125 columns 83–86, row 125 columns 87–89, row 125 columns 90–339, row 126 columns
0–24, row 126 columns 25–28, row 126 columns 29–34, row 126 columns 35–53, row 126 columns 54–57, row 126 columns
58–59, row 126 columns 60–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_3337 : rowsJ2 125 126 73 74 ≤ 3007600276807 := by decide +kernel

theorem rows22250R_3338 : rowsJ2 125 126 74 76 ≤ 4345284503962 := by decide +kernel

theorem rows22250R_3339 : rowsJ2 125 126 76 79 ≤ 3077321117689 := by decide +kernel

theorem rows22250R_3340 : rowsJ2 125 126 79 83 ≤ 901448122768 := by decide +kernel

theorem rows22250R_3341 : rowsJ2 125 126 83 87 ≤ 10375273114183 := by decide +kernel

theorem rows22250R_3342 : rowsJ2 125 126 87 90 ≤ 19329605800482 := by decide +kernel

theorem rows22250R_3343 : rowsJ2 125 126 90 340 ≤ 1016201191643660 := by decide +kernel

theorem rows22250R_3344 : rowsJ2 126 127 0 25 ≤ 3605838229941 := by decide +kernel

theorem rows22250R_3345 : rowsJ2 126 127 25 29 ≤ 17048217508224 := by decide +kernel

theorem rows22250R_3346 : rowsJ2 126 127 29 35 ≤ 13556529835491 := by decide +kernel

theorem rows22250R_3347 : rowsJ2 126 127 35 54 ≤ 2517287658513 := by decide +kernel

theorem rows22250R_3348 : rowsJ2 126 127 54 58 ≤ 6073185802555 := by decide +kernel

theorem rows22250R_3349 : rowsJ2 126 127 58 60 ≤ 5828806173541 := by decide +kernel

theorem rows22250R_3350 : rowsJ2 126 127 60 61 ≤ 3743817850122 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3337
#print axioms SieveCert.rows22250R_3350
