/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4037–4050 of 5066

File 319 of 387: the parts `rows22240R_4037` … `rows22240R_4050` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 98734 in units of a depth-4 test: row 140 columns 65–65, row 140
columns 66–66, row 140 columns 67–67, row 140 columns 68–68, row 140 columns 69–69, row 140 columns 70–70, row 140
columns 71–71, row 140 columns 72–72, row 140 columns 73–74, row 140 columns 75–76, row 140 columns 77–80, row 140
columns 81–339, row 141 columns 0–23, row 141 columns 24–47), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4037 : rowsJ2 140 141 65 66 ≤ 10752535711231 := by decide +kernel

theorem rows22240R_4038 : rowsJ2 140 141 66 67 ≤ 9644456629948 := by decide +kernel

theorem rows22240R_4039 : rowsJ2 140 141 67 68 ≤ 8589852597381 := by decide +kernel

theorem rows22240R_4040 : rowsJ2 140 141 68 69 ≤ 7607465985763 := by decide +kernel

theorem rows22240R_4041 : rowsJ2 140 141 69 70 ≤ 6674590657007 := by decide +kernel

theorem rows22240R_4042 : rowsJ2 140 141 70 71 ≤ 5810445848687 := by decide +kernel

theorem rows22240R_4043 : rowsJ2 140 141 71 72 ≤ 4992254232632 := by decide +kernel

theorem rows22240R_4044 : rowsJ2 140 141 72 73 ≤ 4239692378247 := by decide +kernel

theorem rows22240R_4045 : rowsJ2 140 141 73 75 ≤ 6478518284210 := by decide +kernel

theorem rows22240R_4046 : rowsJ2 140 141 75 77 ≤ 4228714893704 := by decide +kernel

theorem rows22240R_4047 : rowsJ2 140 141 77 81 ≤ 3655511856731 := by decide +kernel

theorem rows22240R_4048 : rowsJ2 140 141 81 340 ≤ 991626861562213 := by decide +kernel

theorem rows22240R_4049 : rowsJ2 141 142 0 24 ≤ 5133310491762 := by decide +kernel

theorem rows22240R_4050 : rowsJ2 141 142 24 48 ≤ 3396238120519 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4037
#print axioms SieveCert.rows22240R_4050
