/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3442–3457 of 4715

File 266 of 351: the parts `rows22250R_3442` … `rows22250R_3457` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 98643 in units of a depth-4 test: row 129 columns 69–69, row 129
columns 70–70, row 129 columns 71–71, row 129 columns 72–72, row 129 columns 73–73, row 129 columns 74–74, row 129
columns 75–76, row 129 columns 77–78, row 129 columns 79–81, row 129 columns 82–85, row 129 columns 86–88, row 129
columns 89–339, row 130 columns 0–23, row 130 columns 24–28, row 130 columns 29–49, row 130 columns 50–54), each a
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

theorem rows22250R_3442 : rowsJ2 129 130 69 70 ≤ 6593923322600 := by decide +kernel

theorem rows22250R_3443 : rowsJ2 129 130 70 71 ≤ 5802620992231 := by decide +kernel

theorem rows22250R_3444 : rowsJ2 129 130 71 72 ≤ 5077956961614 := by decide +kernel

theorem rows22250R_3445 : rowsJ2 129 130 72 73 ≤ 4395089952506 := by decide +kernel

theorem rows22250R_3446 : rowsJ2 129 130 73 74 ≤ 3776092427968 := by decide +kernel

theorem rows22250R_3447 : rowsJ2 129 130 74 75 ≤ 3195983203864 := by decide +kernel

theorem rows22250R_3448 : rowsJ2 129 130 75 77 ≤ 4872177459275 := by decide +kernel

theorem rows22250R_3449 : rowsJ2 129 130 77 79 ≤ 3154235628298 := by decide +kernel

theorem rows22250R_3450 : rowsJ2 129 130 79 82 ≤ 2307570462322 := by decide +kernel

theorem rows22250R_3451 : rowsJ2 129 130 82 86 ≤ 9318833568907 := by decide +kernel

theorem rows22250R_3452 : rowsJ2 129 130 86 89 ≤ 19458399566412 := by decide +kernel

theorem rows22250R_3453 : rowsJ2 129 130 89 340 ≤ 803132250340646 := by decide +kernel

theorem rows22250R_3454 : rowsJ2 130 131 0 24 ≤ 3035220241027 := by decide +kernel

theorem rows22250R_3455 : rowsJ2 130 131 24 29 ≤ 14596134504067 := by decide +kernel

theorem rows22250R_3456 : rowsJ2 130 131 29 50 ≤ 4136338807752 := by decide +kernel

theorem rows22250R_3457 : rowsJ2 130 131 50 55 ≤ 5249725177913 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3442
#print axioms SieveCert.rows22250R_3457
