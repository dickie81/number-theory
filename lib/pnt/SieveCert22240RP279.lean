/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3467–3483 of 5066

File 279 of 387: the parts `rows22240R_3467` … `rows22240R_3483` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 97576 in units of a depth-4 test: row 121 columns 30–31, row 121
columns 32–34, row 121 columns 35–38, row 121 columns 39–47, row 121 columns 48–58, row 121 columns 59–60, row 121
columns 61–62, row 121 columns 63–63, row 121 columns 64–64, row 121 columns 65–65, row 121 columns 66–66, row 121
columns 67–67, row 121 columns 68–68, row 121 columns 69–69, row 121 columns 70–70, row 121 columns 71–71, row 121
columns 72–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3467 : rowsJ2 121 122 30 32 ≤ 17003700013581 := by decide +kernel

theorem rows22240R_3468 : rowsJ2 121 122 32 35 ≤ 20109055507682 := by decide +kernel

theorem rows22240R_3469 : rowsJ2 121 122 35 39 ≤ 14735904878520 := by decide +kernel

theorem rows22240R_3470 : rowsJ2 121 122 39 48 ≤ 2359806218808 := by decide +kernel

theorem rows22240R_3471 : rowsJ2 121 122 48 59 ≤ 3249611486806 := by decide +kernel

theorem rows22240R_3472 : rowsJ2 121 122 59 61 ≤ 3558541664720 := by decide +kernel

theorem rows22240R_3473 : rowsJ2 121 122 61 63 ≤ 5245227805713 := by decide +kernel

theorem rows22240R_3474 : rowsJ2 121 122 63 64 ≤ 3136388032303 := by decide +kernel

theorem rows22240R_3475 : rowsJ2 121 122 64 65 ≤ 3405466881823 := by decide +kernel

theorem rows22240R_3476 : rowsJ2 121 122 65 66 ≤ 3601400970208 := by decide +kernel

theorem rows22240R_3477 : rowsJ2 121 122 66 67 ≤ 3746266227374 := by decide +kernel

theorem rows22240R_3478 : rowsJ2 121 122 67 68 ≤ 3816030717606 := by decide +kernel

theorem rows22240R_3479 : rowsJ2 121 122 68 69 ≤ 3832823116837 := by decide +kernel

theorem rows22240R_3480 : rowsJ2 121 122 69 70 ≤ 3772017550354 := by decide +kernel

theorem rows22240R_3481 : rowsJ2 121 122 70 71 ≤ 3655565505603 := by decide +kernel

theorem rows22240R_3482 : rowsJ2 121 122 71 72 ≤ 3458162009956 := by decide +kernel

theorem rows22240R_3483 : rowsJ2 121 122 72 73 ≤ 3201652543318 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3467
#print axioms SieveCert.rows22240R_3483
