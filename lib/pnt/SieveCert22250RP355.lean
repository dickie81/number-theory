/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4283–4294 of 5796

File 355 of 465: the parts `rows22250R_4283` … `rows22250R_4294` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 93245 tests: row 138 columns 69–69, row 138 columns 70–70, row 138 columns
71–71, row 138 columns 72–72, row 138 columns 73–73, row 138 columns 74–74, row 138 columns 75–75, row 138 columns
76–76, row 138 columns 77–77, row 138 columns 78–78, row 138 columns 79–79, row 138 columns 80–80), each a sum of
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

theorem rows22250R_4283 : rowsJ2 138 139 69 70 ≤ 7393786845031 := by decide +kernel

theorem rows22250R_4284 : rowsJ2 138 139 70 71 ≤ 7690401590900 := by decide +kernel

theorem rows22250R_4285 : rowsJ2 138 139 71 72 ≤ 7928737238361 := by decide +kernel

theorem rows22250R_4286 : rowsJ2 138 139 72 73 ≤ 7150125546534 := by decide +kernel

theorem rows22250R_4287 : rowsJ2 138 139 73 74 ≤ 6409471274023 := by decide +kernel

theorem rows22250R_4288 : rowsJ2 138 139 74 75 ≤ 5723580160689 := by decide +kernel

theorem rows22250R_4289 : rowsJ2 138 139 75 76 ≤ 5073028256493 := by decide +kernel

theorem rows22250R_4290 : rowsJ2 138 139 76 77 ≤ 4474959430107 := by decide +kernel

theorem rows22250R_4291 : rowsJ2 138 139 77 78 ≤ 3909858589022 := by decide +kernel

theorem rows22250R_4292 : rowsJ2 138 139 78 79 ≤ 3395207720636 := by decide +kernel

theorem rows22250R_4293 : rowsJ2 138 139 79 80 ≤ 2911377262983 := by decide +kernel

theorem rows22250R_4294 : rowsJ2 138 139 80 81 ≤ 2476189140858 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4283
#print axioms SieveCert.rows22250R_4294
