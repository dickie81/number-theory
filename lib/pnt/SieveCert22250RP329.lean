/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4347–4362 of 4715

File 329 of 351: the parts `rows22250R_4347` … `rows22250R_4362` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 96005 in units of a depth-4 test: row 167 columns 54–54, row 167
columns 55–56, row 167 columns 57–58, row 167 columns 59–339, row 168 columns 0–37, row 168 columns 38–39, row 168
columns 40–41, row 168 columns 42–42, row 168 columns 43–43, row 168 columns 44–44, row 168 columns 45–45, row 168
columns 46–46, row 168 columns 47–47, row 168 columns 48–48, row 168 columns 49–49, row 168 columns 50–50), each a
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

theorem rows22250R_4347 : rowsJ2 167 168 54 55 ≤ 10890143294729 := by decide +kernel

theorem rows22250R_4348 : rowsJ2 167 168 55 57 ≤ 17547544136287 := by decide +kernel

theorem rows22250R_4349 : rowsJ2 167 168 57 59 ≤ 12637764769099 := by decide +kernel

theorem rows22250R_4350 : rowsJ2 167 168 59 340 ≤ 2679995666734191 := by decide +kernel

theorem rows22250R_4351 : rowsJ2 168 169 0 38 ≤ 16322575015395 := by decide +kernel

theorem rows22250R_4352 : rowsJ2 168 169 38 40 ≤ 14340852174805 := by decide +kernel

theorem rows22250R_4353 : rowsJ2 168 169 40 42 ≤ 19350815343937 := by decide +kernel

theorem rows22250R_4354 : rowsJ2 168 169 42 43 ≤ 11732868116142 := by decide +kernel

theorem rows22250R_4355 : rowsJ2 168 169 43 44 ≤ 13193878340042 := by decide +kernel

theorem rows22250R_4356 : rowsJ2 168 169 44 45 ≤ 14718716029182 := by decide +kernel

theorem rows22250R_4357 : rowsJ2 168 169 45 46 ≤ 16305150555966 := by decide +kernel

theorem rows22250R_4358 : rowsJ2 168 169 46 47 ≤ 17951209341814 := by decide +kernel

theorem rows22250R_4359 : rowsJ2 168 169 47 48 ≤ 19655165688537 := by decide +kernel

theorem rows22250R_4360 : rowsJ2 168 169 48 49 ≤ 21415528166763 := by decide +kernel

theorem rows22250R_4361 : rowsJ2 168 169 49 50 ≤ 19245820142903 := by decide +kernel

theorem rows22250R_4362 : rowsJ2 168 169 50 51 ≤ 17211198530849 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4347
#print axioms SieveCert.rows22250R_4362
