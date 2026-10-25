/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4244–4255 of 5796

File 352 of 465: the parts `rows22250R_4244` … `rows22250R_4255` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 99646 tests: row 137 columns 62–62, row 137 columns 63–63, row 137 columns
64–64, row 137 columns 65–65, row 137 columns 66–66, row 137 columns 67–67, row 137 columns 68–68, row 137 columns
69–69, row 137 columns 70–70, row 137 columns 71–71, row 137 columns 72–72, row 137 columns 73–73), each a sum of
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

theorem rows22250R_4244 : rowsJ2 137 138 62 63 ≤ 3715250048459 := by decide +kernel

theorem rows22250R_4245 : rowsJ2 137 138 63 64 ≤ 4275671641084 := by decide +kernel

theorem rows22250R_4246 : rowsJ2 137 138 64 65 ≤ 4833082056574 := by decide +kernel

theorem rows22250R_4247 : rowsJ2 137 138 65 66 ≤ 5335038827598 := by decide +kernel

theorem rows22250R_4248 : rowsJ2 137 138 66 67 ≤ 5798746316252 := by decide +kernel

theorem rows22250R_4249 : rowsJ2 137 138 67 68 ≤ 6206302127113 := by decide +kernel

theorem rows22250R_4250 : rowsJ2 137 138 68 69 ≤ 6574898749028 := by decide +kernel

theorem rows22250R_4251 : rowsJ2 137 138 69 70 ≤ 6886280652541 := by decide +kernel

theorem rows22250R_4252 : rowsJ2 137 138 70 71 ≤ 7157623212123 := by decide +kernel

theorem rows22250R_4253 : rowsJ2 137 138 71 72 ≤ 7370287923637 := by decide +kernel

theorem rows22250R_4254 : rowsJ2 137 138 72 73 ≤ 7079261747237 := by decide +kernel

theorem rows22250R_4255 : rowsJ2 137 138 73 74 ≤ 6339301541633 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4244
#print axioms SieveCert.rows22250R_4255
