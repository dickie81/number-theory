/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3960–3972 of 4715

File 303 of 351: the parts `rows22250R_3960` … `rows22250R_3972` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 96121 tests: row 149 columns 55–55, row 149 columns 56–56, row 149 columns
57–57, row 149 columns 58–58, row 149 columns 59–59, row 149 columns 60–60, row 149 columns 61–61, row 149 columns
62–62, row 149 columns 63–63, row 149 columns 64–64, row 149 columns 65–65, row 149 columns 66–67, row 149 columns
68–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3960 : rowsJ2 149 150 55 56 ≤ 12048373553578 := by decide +kernel

theorem rows22250R_3961 : rowsJ2 149 150 56 57 ≤ 13239269026691 := by decide +kernel

theorem rows22250R_3962 : rowsJ2 149 150 57 58 ≤ 14471660384743 := by decide +kernel

theorem rows22250R_3963 : rowsJ2 149 150 58 59 ≤ 14333877230934 := by decide +kernel

theorem rows22250R_3964 : rowsJ2 149 150 59 60 ≤ 12864686332483 := by decide +kernel

theorem rows22250R_3965 : rowsJ2 149 150 60 61 ≤ 11485534539525 := by decide +kernel

theorem rows22250R_3966 : rowsJ2 149 150 61 62 ≤ 10193966937718 := by decide +kernel

theorem rows22250R_3967 : rowsJ2 149 150 62 63 ≤ 8987702262855 := by decide +kernel

theorem rows22250R_3968 : rowsJ2 149 150 63 64 ≤ 7864624803801 := by decide +kernel

theorem rows22250R_3969 : rowsJ2 149 150 64 65 ≤ 6822777042507 := by decide +kernel

theorem rows22250R_3970 : rowsJ2 149 150 65 66 ≤ 5860352981017 := by decide +kernel

theorem rows22250R_3971 : rowsJ2 149 150 66 68 ≤ 9142966095394 := by decide +kernel

theorem rows22250R_3972 : rowsJ2 149 150 68 70 ≤ 6207469221044 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3960
#print axioms SieveCert.rows22250R_3972
