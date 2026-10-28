/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3382–3397 of 4715

File 262 of 351: the parts `rows22250R_3382` … `rows22250R_3397` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 99605 in units of a depth-4 test: row 127 columns 65–65, row 127
columns 66–66, row 127 columns 67–67, row 127 columns 68–68, row 127 columns 69–69, row 127 columns 70–70, row 127
columns 71–71, row 127 columns 72–72, row 127 columns 73–73, row 127 columns 74–75, row 127 columns 76–77, row 127
columns 78–80, row 127 columns 81–84, row 127 columns 85–87, row 127 columns 88–99, row 127 columns 100–339), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3382 : rowsJ2 127 128 65 66 ≤ 6184965744429 := by decide +kernel

theorem rows22250R_3383 : rowsJ2 127 128 66 67 ≤ 6406634892272 := by decide +kernel

theorem rows22250R_3384 : rowsJ2 127 128 67 68 ≤ 6575852962279 := by decide +kernel

theorem rows22250R_3385 : rowsJ2 127 128 68 69 ≤ 6668330374059 := by decide +kernel

theorem rows22250R_3386 : rowsJ2 127 128 69 70 ≤ 6285454239283 := by decide +kernel

theorem rows22250R_3387 : rowsJ2 127 128 70 71 ≤ 5495839356096 := by decide +kernel

theorem rows22250R_3388 : rowsJ2 127 128 71 72 ≤ 4772927283339 := by decide +kernel

theorem rows22250R_3389 : rowsJ2 127 128 72 73 ≤ 4091606047837 := by decide +kernel

theorem rows22250R_3390 : rowsJ2 127 128 73 74 ≤ 3474215519472 := by decide +kernel

theorem rows22250R_3391 : rowsJ2 127 128 74 76 ≤ 5273765752343 := by decide +kernel

theorem rows22250R_3392 : rowsJ2 127 128 76 78 ≤ 3372298150761 := by decide +kernel

theorem rows22250R_3393 : rowsJ2 127 128 78 81 ≤ 2300462306628 := by decide +kernel

theorem rows22250R_3394 : rowsJ2 127 128 81 85 ≤ 4734812812356 := by decide +kernel

theorem rows22250R_3395 : rowsJ2 127 128 85 88 ≤ 13641510443374 := by decide +kernel

theorem rows22250R_3396 : rowsJ2 127 128 88 100 ≤ 834513701754739 := by decide +kernel

theorem rows22250R_3397 : rowsJ2 127 128 100 340 ≤ 84248377786305 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3382
#print axioms SieveCert.rows22250R_3397
