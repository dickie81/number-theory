/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1379–1390 of 4715

File 123 of 351: the parts `rows22250R_1379` … `rows22250R_1390` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 89447 in units of a depth-4 test: row 71 columns 40–41, row 71 columns
42–42, row 71 columns 43–43, row 71 columns 44–44, row 71 columns 45–45, row 71 columns 46–46, row 71 columns 47–47,
row 71 columns 48–48, row 71 columns 49–49, row 71 columns 50–50, row 71 columns 51–51, row 71 columns 52–52), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22250R_1379 : rowsJ2 71 72 40 42 ≤ 0 := by decide +kernel

theorem rows22250R_1380 : rowsJ2 71 72 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1381 : rowsJ2 71 72 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1382 : rowsJ2 71 72 44 45 ≤ 62512610724 := by decide +kernel

theorem rows22250R_1383 : rowsJ2 71 72 45 46 ≤ 245362143815 := by decide +kernel

theorem rows22250R_1384 : rowsJ2 71 72 46 47 ≤ 732000827096 := by decide +kernel

theorem rows22250R_1385 : rowsJ2 71 72 47 48 ≤ 1453640097395 := by decide +kernel

theorem rows22250R_1386 : rowsJ2 71 72 48 49 ≤ 2147970878954 := by decide +kernel

theorem rows22250R_1387 : rowsJ2 71 72 49 50 ≤ 2887511887443 := by decide +kernel

theorem rows22250R_1388 : rowsJ2 71 72 50 51 ≤ 3645913455635 := by decide +kernel

theorem rows22250R_1389 : rowsJ2 71 72 51 52 ≤ 4371949003007 := by decide +kernel

theorem rows22250R_1390 : rowsJ2 71 72 52 53 ≤ 4854388418919 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1379
#print axioms SieveCert.rows22250R_1390
