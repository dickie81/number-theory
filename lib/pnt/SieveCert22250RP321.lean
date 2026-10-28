/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4224–4237 of 4715

File 321 of 351: the parts `rows22250R_4224` … `rows22250R_4237` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 93876 in units of a depth-4 test: row 161 columns 49–49, row 161
columns 50–50, row 161 columns 51–51, row 161 columns 52–52, row 161 columns 53–53, row 161 columns 54–54, row 161
columns 55–55, row 161 columns 56–56, row 161 columns 57–57, row 161 columns 58–58, row 161 columns 59–60, row 161
columns 61–63, row 161 columns 64–339, row 162 columns 0–39), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4224 : rowsJ2 161 162 49 50 ≤ 14946145476944 := by decide +kernel

theorem rows22250R_4225 : rowsJ2 161 162 50 51 ≤ 16413300641366 := by decide +kernel

theorem rows22250R_4226 : rowsJ2 161 162 51 52 ≤ 17930852376777 := by decide +kernel

theorem rows22250R_4227 : rowsJ2 161 162 52 53 ≤ 17749791448351 := by decide +kernel

theorem rows22250R_4228 : rowsJ2 161 162 53 54 ≤ 15921059859947 := by decide +kernel

theorem rows22250R_4229 : rowsJ2 161 162 54 55 ≤ 14206472709148 := by decide +kernel

theorem rows22250R_4230 : rowsJ2 161 162 55 56 ≤ 12602575333993 := by decide +kernel

theorem rows22250R_4231 : rowsJ2 161 162 56 57 ≤ 11106168569871 := by decide +kernel

theorem rows22250R_4232 : rowsJ2 161 162 57 58 ≤ 9714295515268 := by decide +kernel

theorem rows22250R_4233 : rowsJ2 161 162 58 59 ≤ 8424229567055 := by decide +kernel

theorem rows22250R_4234 : rowsJ2 161 162 59 61 ≤ 13373164034418 := by decide +kernel

theorem rows22250R_4235 : rowsJ2 161 162 61 64 ≤ 12796259685618 := by decide +kernel

theorem rows22250R_4236 : rowsJ2 161 162 64 340 ≤ 2637707405221586 := by decide +kernel

theorem rows22250R_4237 : rowsJ2 162 163 0 40 ≤ 12568980621372 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4224
#print axioms SieveCert.rows22250R_4237
