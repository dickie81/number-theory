/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3547–3561 of 5796

File 306 of 465: the parts `rows22250R_3547` … `rows22250R_3561` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 93306 tests: row 115 columns 0–25, row 115 columns 26–31, row 115 columns
32–33, row 115 columns 34–35, row 115 columns 36–36, row 115 columns 37–37, row 115 columns 38–38, row 115 columns
39–39, row 115 columns 40–40, row 115 columns 41–42, row 115 columns 43–44, row 115 columns 45–46, row 115 columns
47–49, row 115 columns 50–54, row 115 columns 55–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_3547 : rowsJ2 115 116 0 26 ≤ 0 := by decide +kernel

theorem rows22250R_3548 : rowsJ2 115 116 26 32 ≤ 4356085601182 := by decide +kernel

theorem rows22250R_3549 : rowsJ2 115 116 32 34 ≤ 7815469730260 := by decide +kernel

theorem rows22250R_3550 : rowsJ2 115 116 34 36 ≤ 13831622447013 := by decide +kernel

theorem rows22250R_3551 : rowsJ2 115 116 36 37 ≤ 9358911369966 := by decide +kernel

theorem rows22250R_3552 : rowsJ2 115 116 37 38 ≤ 11186700372531 := by decide +kernel

theorem rows22250R_3553 : rowsJ2 115 116 38 39 ≤ 11714227946088 := by decide +kernel

theorem rows22250R_3554 : rowsJ2 115 116 39 40 ≤ 10705492726711 := by decide +kernel

theorem rows22250R_3555 : rowsJ2 115 116 40 41 ≤ 9109324196264 := by decide +kernel

theorem rows22250R_3556 : rowsJ2 115 116 41 43 ≤ 14106860602316 := by decide +kernel

theorem rows22250R_3557 : rowsJ2 115 116 43 45 ≤ 9629742621502 := by decide +kernel

theorem rows22250R_3558 : rowsJ2 115 116 45 47 ≤ 5827807363377 := by decide +kernel

theorem rows22250R_3559 : rowsJ2 115 116 47 50 ≤ 3264479406201 := by decide +kernel

theorem rows22250R_3560 : rowsJ2 115 116 50 55 ≤ 319540001002 := by decide +kernel

theorem rows22250R_3561 : rowsJ2 115 116 55 65 ≤ 372296989457 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3547
#print axioms SieveCert.rows22250R_3561
