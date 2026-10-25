/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1391–1399 of 4715

File 124 of 351: the parts `rows22250R_1391` … `rows22250R_1399` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 95219 tests: row 71 columns 53–53, row 71 columns 54–54, row 71 columns
55–55, row 71 columns 56–56, row 71 columns 57–57, row 71 columns 58–58, row 71 columns 59–59, row 71 columns 60–60,
row 71 columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1391 : rowsJ2 71 72 53 54 ≤ 5169958697233 := by decide +kernel

theorem rows22250R_1392 : rowsJ2 71 72 54 55 ≤ 5496767465580 := by decide +kernel

theorem rows22250R_1393 : rowsJ2 71 72 55 56 ≤ 5091592552175 := by decide +kernel

theorem rows22250R_1394 : rowsJ2 71 72 56 57 ≤ 4743216632998 := by decide +kernel

theorem rows22250R_1395 : rowsJ2 71 72 57 58 ≤ 4398700604353 := by decide +kernel

theorem rows22250R_1396 : rowsJ2 71 72 58 59 ≤ 4110889561830 := by decide +kernel

theorem rows22250R_1397 : rowsJ2 71 72 59 60 ≤ 3826198374214 := by decide +kernel

theorem rows22250R_1398 : rowsJ2 71 72 60 61 ≤ 3534527361243 := by decide +kernel

theorem rows22250R_1399 : rowsJ2 71 72 61 62 ≤ 3245750658797 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1391
#print axioms SieveCert.rows22250R_1399
