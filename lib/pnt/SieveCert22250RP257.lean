/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3307–3320 of 4715

File 257 of 351: the parts `rows22250R_3307` … `rows22250R_3320` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 93092 tests: row 124 columns 69–69, row 124 columns 70–70, row 124 columns
71–71, row 124 columns 72–72, row 124 columns 73–74, row 124 columns 75–76, row 124 columns 77–80, row 124 columns
81–84, row 124 columns 85–87, row 124 columns 88–90, row 124 columns 91–339, row 125 columns 0–24, row 125 columns
25–28, row 125 columns 29–33), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_3307 : rowsJ2 124 125 69 70 ≤ 4856075743881 := by decide +kernel

theorem rows22250R_3308 : rowsJ2 124 125 70 71 ≤ 4717498015802 := by decide +kernel

theorem rows22250R_3309 : rowsJ2 124 125 71 72 ≤ 3997633255019 := by decide +kernel

theorem rows22250R_3310 : rowsJ2 124 125 72 73 ≤ 3319034362377 := by decide +kernel

theorem rows22250R_3311 : rowsJ2 124 125 73 75 ≤ 4832667788185 := by decide +kernel

theorem rows22250R_3312 : rowsJ2 124 125 75 77 ≤ 2748098320679 := by decide +kernel

theorem rows22250R_3313 : rowsJ2 124 125 77 81 ≤ 1043728536417 := by decide +kernel

theorem rows22250R_3314 : rowsJ2 124 125 81 85 ≤ 3664500975817 := by decide +kernel

theorem rows22250R_3315 : rowsJ2 124 125 85 88 ≤ 11409660218527 := by decide +kernel

theorem rows22250R_3316 : rowsJ2 124 125 88 91 ≤ 22190318760027 := by decide +kernel

theorem rows22250R_3317 : rowsJ2 124 125 91 340 ≤ 1022378539761489 := by decide +kernel

theorem rows22250R_3318 : rowsJ2 125 126 0 25 ≤ 3078495256404 := by decide +kernel

theorem rows22250R_3319 : rowsJ2 125 126 25 29 ≤ 17923851015010 := by decide +kernel

theorem rows22250R_3320 : rowsJ2 125 126 29 34 ≤ 15240183045943 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3307
#print axioms SieveCert.rows22250R_3320
