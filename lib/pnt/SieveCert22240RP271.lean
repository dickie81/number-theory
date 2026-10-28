/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3345–3359 of 5066

File 271 of 387: the parts `rows22240R_3345` … `rows22240R_3359` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 96193 in units of a depth-4 test: row 116 columns 68–69, row 116
columns 70–72, row 116 columns 73–75, row 116 columns 76–78, row 116 columns 79–81, row 116 columns 82–84, row 116
columns 85–87, row 116 columns 88–89, row 116 columns 90–91, row 116 columns 92–93, row 116 columns 94–94, row 116
columns 95–95, row 116 columns 96–339, row 117 columns 0–26, row 117 columns 27–29), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3345 : rowsJ2 116 117 68 70 ≤ 3226408054078 := by decide +kernel

theorem rows22240R_3346 : rowsJ2 116 117 70 73 ≤ 2645634191937 := by decide +kernel

theorem rows22240R_3347 : rowsJ2 116 117 73 76 ≤ 0 := by decide +kernel

theorem rows22240R_3348 : rowsJ2 116 117 76 79 ≤ 0 := by decide +kernel

theorem rows22240R_3349 : rowsJ2 116 117 79 82 ≤ 246625409806 := by decide +kernel

theorem rows22240R_3350 : rowsJ2 116 117 82 85 ≤ 2909880131253 := by decide +kernel

theorem rows22240R_3351 : rowsJ2 116 117 85 88 ≤ 7944500011000 := by decide +kernel

theorem rows22240R_3352 : rowsJ2 116 117 88 90 ≤ 9246983151119 := by decide +kernel

theorem rows22240R_3353 : rowsJ2 116 117 90 92 ≤ 13287034326410 := by decide +kernel

theorem rows22240R_3354 : rowsJ2 116 117 92 94 ≤ 18134081862277 := by decide +kernel

theorem rows22240R_3355 : rowsJ2 116 117 94 95 ≤ 11145459323313 := by decide +kernel

theorem rows22240R_3356 : rowsJ2 116 117 95 96 ≤ 12701023277010 := by decide +kernel

theorem rows22240R_3357 : rowsJ2 116 117 96 340 ≤ 1555359875832759 := by decide +kernel

theorem rows22240R_3358 : rowsJ2 117 118 0 27 ≤ 1177407160106 := by decide +kernel

theorem rows22240R_3359 : rowsJ2 117 118 27 30 ≤ 8635130212889 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3345
#print axioms SieveCert.rows22240R_3359
