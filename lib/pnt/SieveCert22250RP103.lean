/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1128–1139 of 4715

File 103 of 351: the parts `rows22250R_1128` … `rows22250R_1139` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 98114 tests: row 65 columns 60–60, row 65 columns 61–61, row 65 columns
62–62, row 65 columns 63–63, row 65 columns 64–64, row 65 columns 65–339, row 66 columns 0–17, row 66 columns 18–20,
row 66 columns 21–21, row 66 columns 22–22, row 66 columns 23–23, row 66 columns 24–24), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1128 : rowsJ2 65 66 60 61 ≤ 8675981785869 := by decide +kernel

theorem rows22250R_1129 : rowsJ2 65 66 61 62 ≤ 8214095447123 := by decide +kernel

theorem rows22250R_1130 : rowsJ2 65 66 62 63 ≤ 7741095450571 := by decide +kernel

theorem rows22250R_1131 : rowsJ2 65 66 63 64 ≤ 7273025648989 := by decide +kernel

theorem rows22250R_1132 : rowsJ2 65 66 64 65 ≤ 6793042871642 := by decide +kernel

theorem rows22250R_1133 : rowsJ2 65 66 65 340 ≤ 6317635130642 := by decide +kernel

theorem rows22250R_1134 : rowsJ2 66 67 0 18 ≤ 1448212407562 := by decide +kernel

theorem rows22250R_1135 : rowsJ2 66 67 18 21 ≤ 14205173414 := by decide +kernel

theorem rows22250R_1136 : rowsJ2 66 67 21 22 ≤ 0 := by decide +kernel

theorem rows22250R_1137 : rowsJ2 66 67 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1138 : rowsJ2 66 67 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1139 : rowsJ2 66 67 24 25 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1128
#print axioms SieveCert.rows22250R_1139
