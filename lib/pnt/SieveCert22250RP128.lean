/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1441–1452 of 4715

File 128 of 351: the parts `rows22250R_1441` … `rows22250R_1452` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 94946 in units of a depth-4 test: row 72 columns 57–57, row 72 columns
58–58, row 72 columns 59–59, row 72 columns 60–60, row 72 columns 61–61, row 72 columns 62–62, row 72 columns 63–63,
row 72 columns 64–64, row 72 columns 65–65, row 72 columns 66–66, row 72 columns 67–67, row 72 columns 68–68), each
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

theorem rows22250R_1441 : rowsJ2 72 73 57 58 ≤ 3662013500333 := by decide +kernel

theorem rows22250R_1442 : rowsJ2 72 73 58 59 ≤ 3376013257896 := by decide +kernel

theorem rows22250R_1443 : rowsJ2 72 73 59 60 ≤ 3146774778067 := by decide +kernel

theorem rows22250R_1444 : rowsJ2 72 73 60 61 ≤ 2856759531169 := by decide +kernel

theorem rows22250R_1445 : rowsJ2 72 73 61 62 ≤ 2624082098294 := by decide +kernel

theorem rows22250R_1446 : rowsJ2 72 73 62 63 ≤ 2329371094364 := by decide +kernel

theorem rows22250R_1447 : rowsJ2 72 73 63 64 ≤ 2092623709478 := by decide +kernel

theorem rows22250R_1448 : rowsJ2 72 73 64 65 ≤ 1792516215392 := by decide +kernel

theorem rows22250R_1449 : rowsJ2 72 73 65 66 ≤ 1551047855015 := by decide +kernel

theorem rows22250R_1450 : rowsJ2 72 73 66 67 ≤ 1244818568699 := by decide +kernel

theorem rows22250R_1451 : rowsJ2 72 73 67 68 ≤ 997953716459 := by decide +kernel

theorem rows22250R_1452 : rowsJ2 72 73 68 69 ≤ 752711734700 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1441
#print axioms SieveCert.rows22250R_1452
