/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5073–5084 of 5796

File 417 of 465: the parts `rows22250R_5073` … `rows22250R_5084` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 95905 tests: row 165 columns 56–56, row 165 columns 57–57, row 165 columns
58–58, row 165 columns 59–59, row 165 columns 60–60, row 165 columns 61–61, row 165 columns 62–62, row 165 columns
63–63, row 165 columns 64–64, row 165 columns 65–65, row 165 columns 66–66, row 165 columns 67–68), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5073 : rowsJ2 165 166 56 57 ≤ 13799270780824 := by decide +kernel

theorem rows22250R_5074 : rowsJ2 165 166 57 58 ≤ 14982684588196 := by decide +kernel

theorem rows22250R_5075 : rowsJ2 165 166 58 59 ≤ 14843697025516 := by decide +kernel

theorem rows22250R_5076 : rowsJ2 165 166 59 60 ≤ 13418771787037 := by decide +kernel

theorem rows22250R_5077 : rowsJ2 165 166 60 61 ≤ 12076246915534 := by decide +kernel

theorem rows22250R_5078 : rowsJ2 165 166 61 62 ≤ 10813840581040 := by decide +kernel

theorem rows22250R_5079 : rowsJ2 165 166 62 63 ≤ 9629426335178 := by decide +kernel

theorem rows22250R_5080 : rowsJ2 165 166 63 64 ≤ 8521025719188 := by decide +kernel

theorem rows22250R_5081 : rowsJ2 165 166 64 65 ≤ 7486801523268 := by decide +kernel

theorem rows22250R_5082 : rowsJ2 165 166 65 66 ≤ 6525051652155 := by decide +kernel

theorem rows22250R_5083 : rowsJ2 165 166 66 67 ≤ 5634203555647 := by decide +kernel

theorem rows22250R_5084 : rowsJ2 165 166 67 69 ≤ 8872349657429 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5073
#print axioms SieveCert.rows22250R_5084
