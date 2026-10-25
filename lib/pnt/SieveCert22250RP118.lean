/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1135–1140 of 5796

File 118 of 465: the parts `rows22250R_1135` … `rows22250R_1140` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 96905 tests: row 65 columns 59–59, row 65 columns 60–60, row 65 columns
61–61, row 65 columns 62–62, row 65 columns 63–63, row 65 columns 64–64), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1135 : rowsJ2 65 66 59 60 ≤ 9530389542713 := by decide +kernel

theorem rows22250R_1136 : rowsJ2 65 66 60 61 ≤ 10419518146142 := by decide +kernel

theorem rows22250R_1137 : rowsJ2 65 66 61 62 ≤ 11160654324708 := by decide +kernel

theorem rows22250R_1138 : rowsJ2 65 66 62 63 ≤ 11710806488846 := by decide +kernel

theorem rows22250R_1139 : rowsJ2 65 66 63 64 ≤ 11704809165017 := by decide +kernel

theorem rows22250R_1140 : rowsJ2 65 66 64 65 ≤ 11193555525545 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1135
#print axioms SieveCert.rows22250R_1140
