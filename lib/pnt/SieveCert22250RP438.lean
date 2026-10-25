/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5367–5380 of 5796

File 438 of 465: the parts `rows22250R_5367` … `rows22250R_5380` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98593 tests: row 178 columns 0–38, row 178 columns 39–41, row 178 columns
42–43, row 178 columns 44–44, row 178 columns 45–45, row 178 columns 46–46, row 178 columns 47–47, row 178 columns
48–48, row 178 columns 49–49, row 178 columns 50–50, row 178 columns 51–51, row 178 columns 52–52, row 178 columns
53–53, row 178 columns 54–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_5367 : rowsJ2 178 179 0 39 ≤ 8552743312913 := by decide +kernel

theorem rows22250R_5368 : rowsJ2 178 179 39 42 ≤ 17502456236999 := by decide +kernel

theorem rows22250R_5369 : rowsJ2 178 179 42 44 ≤ 16815350221738 := by decide +kernel

theorem rows22250R_5370 : rowsJ2 178 179 44 45 ≤ 10127319955675 := by decide +kernel

theorem rows22250R_5371 : rowsJ2 178 179 45 46 ≤ 11346258371282 := by decide +kernel

theorem rows22250R_5372 : rowsJ2 178 179 46 47 ≤ 12617065615441 := by decide +kernel

theorem rows22250R_5373 : rowsJ2 178 179 47 48 ≤ 13937972582478 := by decide +kernel

theorem rows22250R_5374 : rowsJ2 178 179 48 49 ≤ 15307399295319 := by decide +kernel

theorem rows22250R_5375 : rowsJ2 178 179 49 50 ≤ 16723946166550 := by decide +kernel

theorem rows22250R_5376 : rowsJ2 178 179 50 51 ≤ 18186386286458 := by decide +kernel

theorem rows22250R_5377 : rowsJ2 178 179 51 52 ≤ 19693658686697 := by decide +kernel

theorem rows22250R_5378 : rowsJ2 178 179 52 53 ≤ 17829085484894 := by decide +kernel

theorem rows22250R_5379 : rowsJ2 178 179 53 54 ≤ 16073201006301 := by decide +kernel

theorem rows22250R_5380 : rowsJ2 178 179 54 55 ≤ 14422567814016 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5367
#print axioms SieveCert.rows22250R_5380
