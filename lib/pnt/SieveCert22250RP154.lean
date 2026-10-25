/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1525–1532 of 5796

File 154 of 465: the parts `rows22250R_1525` … `rows22250R_1532` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 97174 tests: row 73 columns 60–60, row 73 columns 61–61, row 73 columns
62–62, row 73 columns 63–63, row 73 columns 64–64, row 73 columns 65–65, row 73 columns 66–66, row 73 columns
67–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1525 : rowsJ2 73 74 60 61 ≤ 5514244379429 := by decide +kernel

theorem rows22250R_1526 : rowsJ2 73 74 61 62 ≤ 5191392045560 := by decide +kernel

theorem rows22250R_1527 : rowsJ2 73 74 62 63 ≤ 4871922507854 := by decide +kernel

theorem rows22250R_1528 : rowsJ2 73 74 63 64 ≤ 4545221931201 := by decide +kernel

theorem rows22250R_1529 : rowsJ2 73 74 64 65 ≤ 4221677750301 := by decide +kernel

theorem rows22250R_1530 : rowsJ2 73 74 65 66 ≤ 3890409221812 := by decide +kernel

theorem rows22250R_1531 : rowsJ2 73 74 66 67 ≤ 3562070025392 := by decide +kernel

theorem rows22250R_1532 : rowsJ2 73 74 67 68 ≤ 3279526528047 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1525
#print axioms SieveCert.rows22250R_1532
