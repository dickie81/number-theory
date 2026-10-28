/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3129–3144 of 5066

File 257 of 387: the parts `rows22240R_3129` … `rows22240R_3144` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 95838 in units of a depth-4 test: row 108 columns 98–98, row 108
columns 99–99, row 108 columns 100–339, row 109 columns 0–23, row 109 columns 24–30, row 109 columns 31–32, row 109
columns 33–34, row 109 columns 35–35, row 109 columns 36–36, row 109 columns 37–37, row 109 columns 38–38, row 109
columns 39–40, row 109 columns 41–42, row 109 columns 43–44, row 109 columns 45–47, row 109 columns 48–52), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3129 : rowsJ2 108 109 98 99 ≤ 11928359057147 := by decide +kernel

theorem rows22240R_3130 : rowsJ2 108 109 99 100 ≤ 13428739501459 := by decide +kernel

theorem rows22240R_3131 : rowsJ2 108 109 100 340 ≤ 912745267078210 := by decide +kernel

theorem rows22240R_3132 : rowsJ2 109 110 0 24 ≤ 0 := by decide +kernel

theorem rows22240R_3133 : rowsJ2 109 110 24 31 ≤ 5845995734140 := by decide +kernel

theorem rows22240R_3134 : rowsJ2 109 110 31 33 ≤ 9653348471737 := by decide +kernel

theorem rows22240R_3135 : rowsJ2 109 110 33 35 ≤ 16591670073437 := by decide +kernel

theorem rows22240R_3136 : rowsJ2 109 110 35 36 ≤ 11296228843153 := by decide +kernel

theorem rows22240R_3137 : rowsJ2 109 110 36 37 ≤ 13895332050467 := by decide +kernel

theorem rows22240R_3138 : rowsJ2 109 110 37 38 ≤ 14661042484582 := by decide +kernel

theorem rows22240R_3139 : rowsJ2 109 110 38 39 ≤ 12607654123745 := by decide +kernel

theorem rows22240R_3140 : rowsJ2 109 110 39 41 ≤ 19544546181621 := by decide +kernel

theorem rows22240R_3141 : rowsJ2 109 110 41 43 ≤ 13362391079279 := by decide +kernel

theorem rows22240R_3142 : rowsJ2 109 110 43 45 ≤ 8668275677287 := by decide +kernel

theorem rows22240R_3143 : rowsJ2 109 110 45 48 ≤ 5968254167023 := by decide +kernel

theorem rows22240R_3144 : rowsJ2 109 110 48 53 ≤ 779815671272 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3129
#print axioms SieveCert.rows22240R_3144
