/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4000–4010 of 5066

File 316 of 387: the parts `rows22240R_4000` … `rows22240R_4010` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 95199 in units of a depth-4 test: row 139 columns 56–56, row 139
columns 57–57, row 139 columns 58–58, row 139 columns 59–59, row 139 columns 60–60, row 139 columns 61–61, row 139
columns 62–62, row 139 columns 63–63, row 139 columns 64–64, row 139 columns 65–65, row 139 columns 66–66), each a
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

theorem rows22240R_4000 : rowsJ2 139 140 56 57 ≤ 6076517018908 := by decide +kernel

theorem rows22240R_4001 : rowsJ2 139 140 57 58 ≤ 6910492799210 := by decide +kernel

theorem rows22240R_4002 : rowsJ2 139 140 58 59 ≤ 7786113306748 := by decide +kernel

theorem rows22240R_4003 : rowsJ2 139 140 59 60 ≤ 8701765106283 := by decide +kernel

theorem rows22240R_4004 : rowsJ2 139 140 60 61 ≤ 9655940164391 := by decide +kernel

theorem rows22240R_4005 : rowsJ2 139 140 61 62 ≤ 10627149881404 := by decide +kernel

theorem rows22240R_4006 : rowsJ2 139 140 62 63 ≤ 11554560988208 := by decide +kernel

theorem rows22240R_4007 : rowsJ2 139 140 63 64 ≤ 12417750519834 := by decide +kernel

theorem rows22240R_4008 : rowsJ2 139 140 64 65 ≤ 12222090100141 := by decide +kernel

theorem rows22240R_4009 : rowsJ2 139 140 65 66 ≤ 11038602211319 := by decide +kernel

theorem rows22240R_4010 : rowsJ2 139 140 66 67 ≤ 9931309420995 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4000
#print axioms SieveCert.rows22240R_4010
