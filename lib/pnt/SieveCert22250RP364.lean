/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4399–4412 of 5796

File 364 of 465: the parts `rows22250R_4399` … `rows22250R_4412` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98926 tests: row 142 columns 0–23, row 142 columns 24–29, row 142 columns
30–52, row 142 columns 53–55, row 142 columns 56–57, row 142 columns 58–58, row 142 columns 59–59, row 142 columns
60–60, row 142 columns 61–61, row 142 columns 62–62, row 142 columns 63–63, row 142 columns 64–64, row 142 columns
65–65, row 142 columns 66–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4399 : rowsJ2 142 143 0 24 ≤ 2184476230894 := by decide +kernel

theorem rows22250R_4400 : rowsJ2 142 143 24 30 ≤ 7335481004634 := by decide +kernel

theorem rows22250R_4401 : rowsJ2 142 143 30 53 ≤ 1941023743624 := by decide +kernel

theorem rows22250R_4402 : rowsJ2 142 143 53 56 ≤ 4118219468318 := by decide +kernel

theorem rows22250R_4403 : rowsJ2 142 143 56 58 ≤ 4827138714110 := by decide +kernel

theorem rows22250R_4404 : rowsJ2 142 143 58 59 ≤ 3159350520040 := by decide +kernel

theorem rows22250R_4405 : rowsJ2 142 143 59 60 ≤ 3706512513085 := by decide +kernel

theorem rows22250R_4406 : rowsJ2 142 143 60 61 ≤ 4289272354962 := by decide +kernel

theorem rows22250R_4407 : rowsJ2 142 143 61 62 ≤ 4906245848800 := by decide +kernel

theorem rows22250R_4408 : rowsJ2 142 143 62 63 ≤ 5556144386242 := by decide +kernel

theorem rows22250R_4409 : rowsJ2 142 143 63 64 ≤ 6237770022362 := by decide +kernel

theorem rows22250R_4410 : rowsJ2 142 143 64 65 ≤ 6916355497697 := by decide +kernel

theorem rows22250R_4411 : rowsJ2 142 143 65 66 ≤ 7540918437847 := by decide +kernel

theorem rows22250R_4412 : rowsJ2 142 143 66 67 ≤ 8128308420264 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4399
#print axioms SieveCert.rows22250R_4412
