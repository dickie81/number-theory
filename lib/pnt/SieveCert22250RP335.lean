/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4445–4460 of 4715

File 335 of 351: the parts `rows22250R_4445` … `rows22250R_4460` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 94728 in units of a depth-4 test: row 173 columns 45–45, row 173
columns 46–46, row 173 columns 47–47, row 173 columns 48–48, row 173 columns 49–49, row 173 columns 50–50, row 173
columns 51–52, row 173 columns 53–339, row 174 columns 0–35, row 174 columns 36–37, row 174 columns 38–39, row 174
columns 40–40, row 174 columns 41–41, row 174 columns 42–42, row 174 columns 43–43, row 174 columns 44–44), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4445 : rowsJ2 173 174 45 46 ≤ 22760038626574 := by decide +kernel

theorem rows22250R_4446 : rowsJ2 173 174 46 47 ≤ 22515391593258 := by decide +kernel

theorem rows22250R_4447 : rowsJ2 173 174 47 48 ≤ 20180976187857 := by decide +kernel

theorem rows22250R_4448 : rowsJ2 173 174 48 49 ≤ 17995524589760 := by decide +kernel

theorem rows22250R_4449 : rowsJ2 173 174 49 50 ≤ 15953987151422 := by decide +kernel

theorem rows22250R_4450 : rowsJ2 173 174 50 51 ≤ 14051706945887 := by decide +kernel

theorem rows22250R_4451 : rowsJ2 173 174 51 53 ≤ 22932516494137 := by decide +kernel

theorem rows22250R_4452 : rowsJ2 173 174 53 340 ≤ 2797686971726753 := by decide +kernel

theorem rows22250R_4453 : rowsJ2 174 175 0 36 ≤ 18379299322444 := by decide +kernel

theorem rows22250R_4454 : rowsJ2 174 175 36 38 ≤ 19038296528401 := by decide +kernel

theorem rows22250R_4455 : rowsJ2 174 175 38 40 ≤ 25028901676438 := by decide +kernel

theorem rows22250R_4456 : rowsJ2 174 175 40 41 ≤ 14952334074333 := by decide +kernel

theorem rows22250R_4457 : rowsJ2 174 175 41 42 ≤ 16673691638978 := by decide +kernel

theorem rows22250R_4458 : rowsJ2 174 175 42 43 ≤ 18463975386474 := by decide +kernel

theorem rows22250R_4459 : rowsJ2 174 175 43 44 ≤ 20321040265723 := by decide +kernel

theorem rows22250R_4460 : rowsJ2 174 175 44 45 ≤ 22243036865509 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4445
#print axioms SieveCert.rows22250R_4460
