/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5152–5167 of 5796

File 423 of 465: the parts `rows22250R_5152` … `rows22250R_5167` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96796 tests: row 168 columns 59–59, row 168 columns 60–60, row 168 columns
61–61, row 168 columns 62–62, row 168 columns 63–63, row 168 columns 64–64, row 168 columns 65–65, row 168 columns
66–67, row 168 columns 68–70, row 168 columns 71–359, row 169 columns 0–41, row 169 columns 42–44, row 169 columns
45–46, row 169 columns 47–47, row 169 columns 48–48, row 169 columns 49–49), each a sum of refined costs (`rows2` or
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

theorem rows22250R_5152 : rowsJ2 168 169 59 60 ≤ 12044936534684 := by decide +kernel

theorem rows22250R_5153 : rowsJ2 168 169 60 61 ≤ 10756234260609 := by decide +kernel

theorem rows22250R_5154 : rowsJ2 168 169 61 62 ≤ 9548927367155 := by decide +kernel

theorem rows22250R_5155 : rowsJ2 168 169 62 63 ≤ 8420948778145 := by decide +kernel

theorem rows22250R_5156 : rowsJ2 168 169 63 64 ≤ 7370382594190 := by decide +kernel

theorem rows22250R_5157 : rowsJ2 168 169 64 65 ≤ 6395457527792 := by decide +kernel

theorem rows22250R_5158 : rowsJ2 168 169 65 66 ≤ 5494540959204 := by decide +kernel

theorem rows22250R_5159 : rowsJ2 168 169 66 68 ≤ 8574998117505 := by decide +kernel

theorem rows22250R_5160 : rowsJ2 168 169 68 71 ≤ 7876382331294 := by decide +kernel

theorem rows22250R_5161 : rowsJ2 168 169 71 360 ≤ 2524729693254148 := by decide +kernel

theorem rows22250R_5162 : rowsJ2 169 170 0 42 ≤ 6610101241862 := by decide +kernel

theorem rows22250R_5163 : rowsJ2 169 170 42 45 ≤ 11274009557225 := by decide +kernel

theorem rows22250R_5164 : rowsJ2 169 170 45 47 ≤ 11477448292121 := by decide +kernel

theorem rows22250R_5165 : rowsJ2 169 170 47 48 ≤ 7088506031776 := by decide +kernel

theorem rows22250R_5166 : rowsJ2 169 170 48 49 ≤ 8054762211284 := by decide +kernel

theorem rows22250R_5167 : rowsJ2 169 170 49 50 ≤ 9068347580137 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5152
#print axioms SieveCert.rows22250R_5167
