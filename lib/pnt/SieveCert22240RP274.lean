/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3390–3403 of 5066

File 274 of 387: the parts `rows22240R_3390` … `rows22240R_3403` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 96949 in units of a depth-4 test: row 118 columns 39–43, row 118
columns 44–56, row 118 columns 57–60, row 118 columns 61–62, row 118 columns 63–64, row 118 columns 65–66, row 118
columns 67–68, row 118 columns 69–70, row 118 columns 71–72, row 118 columns 73–74, row 118 columns 75–77, row 118
columns 78–80, row 118 columns 81–83, row 118 columns 84–86), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_3390 : rowsJ2 118 119 39 44 ≤ 7268618485910 := by decide +kernel

theorem rows22240R_3391 : rowsJ2 118 119 44 57 ≤ 520737225608 := by decide +kernel

theorem rows22240R_3392 : rowsJ2 118 119 57 61 ≤ 3475246681457 := by decide +kernel

theorem rows22240R_3393 : rowsJ2 118 119 61 63 ≤ 3687133008149 := by decide +kernel

theorem rows22240R_3394 : rowsJ2 118 119 63 65 ≤ 4658568432761 := by decide +kernel

theorem rows22240R_3395 : rowsJ2 118 119 65 67 ≤ 5132521850251 := by decide +kernel

theorem rows22240R_3396 : rowsJ2 118 119 67 69 ≤ 5094278360985 := by decide +kernel

theorem rows22240R_3397 : rowsJ2 118 119 69 71 ≤ 4524611219657 := by decide +kernel

theorem rows22240R_3398 : rowsJ2 118 119 71 73 ≤ 3397921162980 := by decide +kernel

theorem rows22240R_3399 : rowsJ2 118 119 73 75 ≤ 1682207607414 := by decide +kernel

theorem rows22240R_3400 : rowsJ2 118 119 75 78 ≤ 0 := by decide +kernel

theorem rows22240R_3401 : rowsJ2 118 119 78 81 ≤ 0 := by decide +kernel

theorem rows22240R_3402 : rowsJ2 118 119 81 84 ≤ 2114065218446 := by decide +kernel

theorem rows22240R_3403 : rowsJ2 118 119 84 87 ≤ 7008424255927 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3390
#print axioms SieveCert.rows22240R_3403
