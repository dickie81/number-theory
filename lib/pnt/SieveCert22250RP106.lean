/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1167–1174 of 4715

File 106 of 351: the parts `rows22250R_1167` … `rows22250R_1174` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, work 96854 in units of a depth-4 test: row 66 columns 55–55, row 66 columns
56–56, row 66 columns 57–57, row 66 columns 58–58, row 66 columns 59–59, row 66 columns 60–60, row 66 columns 61–61,
row 66 columns 62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22250R_1167 : rowsJ2 66 67 55 56 ≤ 8484199179803 := by decide +kernel

theorem rows22250R_1168 : rowsJ2 66 67 56 57 ≤ 9018358149896 := by decide +kernel

theorem rows22250R_1169 : rowsJ2 66 67 57 58 ≤ 8989859497445 := by decide +kernel

theorem rows22250R_1170 : rowsJ2 66 67 58 59 ≤ 8531153634458 := by decide +kernel

theorem rows22250R_1171 : rowsJ2 66 67 59 60 ≤ 8129245255872 := by decide +kernel

theorem rows22250R_1172 : rowsJ2 66 67 60 61 ≤ 7665579068029 := by decide +kernel

theorem rows22250R_1173 : rowsJ2 66 67 61 62 ≤ 7259066237986 := by decide +kernel

theorem rows22250R_1174 : rowsJ2 66 67 62 63 ≤ 6789354837875 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1167
#print axioms SieveCert.rows22250R_1174
