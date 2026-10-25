/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4202–4216 of 5796

File 349 of 465: the parts `rows22250R_4202` … `rows22250R_4216` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98306 tests: row 135 columns 91–93, row 135 columns 94–95, row 135 columns
96–359, row 136 columns 0–24, row 136 columns 25–28, row 136 columns 29–33, row 136 columns 34–52, row 136 columns
53–57, row 136 columns 58–59, row 136 columns 60–61, row 136 columns 62–62, row 136 columns 63–63, row 136 columns
64–64, row 136 columns 65–65, row 136 columns 66–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4202 : rowsJ2 135 136 91 94 ≤ 15293578122355 := by decide +kernel

theorem rows22250R_4203 : rowsJ2 135 136 94 96 ≤ 16514525867202 := by decide +kernel

theorem rows22250R_4204 : rowsJ2 135 136 96 360 ≤ 719259458560427 := by decide +kernel

theorem rows22250R_4205 : rowsJ2 136 137 0 25 ≤ 1576865817400 := by decide +kernel

theorem rows22250R_4206 : rowsJ2 136 137 25 29 ≤ 12278537116905 := by decide +kernel

theorem rows22250R_4207 : rowsJ2 136 137 29 34 ≤ 8647378097739 := by decide +kernel

theorem rows22250R_4208 : rowsJ2 136 137 34 53 ≤ 1539676856384 := by decide +kernel

theorem rows22250R_4209 : rowsJ2 136 137 53 58 ≤ 3499608058858 := by decide +kernel

theorem rows22250R_4210 : rowsJ2 136 137 58 60 ≤ 3602441104316 := by decide +kernel

theorem rows22250R_4211 : rowsJ2 136 137 60 62 ≤ 5335653755741 := by decide +kernel

theorem rows22250R_4212 : rowsJ2 136 137 62 63 ≤ 3406465423187 := by decide +kernel

theorem rows22250R_4213 : rowsJ2 136 137 63 64 ≤ 3943377717910 := by decide +kernel

theorem rows22250R_4214 : rowsJ2 136 137 64 65 ≤ 4477314916687 := by decide +kernel

theorem rows22250R_4215 : rowsJ2 136 137 65 66 ≤ 4955534913792 := by decide +kernel

theorem rows22250R_4216 : rowsJ2 136 137 66 67 ≤ 5395317215529 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4202
#print axioms SieveCert.rows22250R_4216
