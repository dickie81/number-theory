/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1264–1272 of 5796

File 130 of 465: the parts `rows22250R_1264` … `rows22250R_1272` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 93411 tests: row 68 columns 49–49, row 68 columns 50–50, row 68 columns
51–51, row 68 columns 52–52, row 68 columns 53–53, row 68 columns 54–54, row 68 columns 55–55, row 68 columns 56–56,
row 68 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22250R_1264 : rowsJ2 68 69 49 50 ≤ 874945163660 := by decide +kernel

theorem rows22250R_1265 : rowsJ2 68 69 50 51 ≤ 1315943390420 := by decide +kernel

theorem rows22250R_1266 : rowsJ2 68 69 51 52 ≤ 1894296177912 := by decide +kernel

theorem rows22250R_1267 : rowsJ2 68 69 52 53 ≤ 2714921477481 := by decide +kernel

theorem rows22250R_1268 : rowsJ2 68 69 53 54 ≤ 3556760830476 := by decide +kernel

theorem rows22250R_1269 : rowsJ2 68 69 54 55 ≤ 4417530515948 := by decide +kernel

theorem rows22250R_1270 : rowsJ2 68 69 55 56 ≤ 5300512538414 := by decide +kernel

theorem rows22250R_1271 : rowsJ2 68 69 56 57 ≤ 6260898964574 := by decide +kernel

theorem rows22250R_1272 : rowsJ2 68 69 57 58 ≤ 7093472962139 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1264
#print axioms SieveCert.rows22250R_1272
