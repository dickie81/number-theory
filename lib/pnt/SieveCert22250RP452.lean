/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5584–5599 of 5796

File 452 of 465: the parts `rows22250R_5584` … `rows22250R_5599` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98086 tests: row 189 columns 50–50, row 189 columns 51–359, row 190 columns
0–35, row 190 columns 36–37, row 190 columns 38–39, row 190 columns 40–40, row 190 columns 41–41, row 190 columns
42–42, row 190 columns 43–43, row 190 columns 44–44, row 190 columns 45–45, row 190 columns 46–46, row 190 columns
47–47, row 190 columns 48–48, row 190 columns 49–49, row 190 columns 50–359), each a sum of refined costs (`rows2`
or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5584 : rowsJ2 189 190 50 51 ≤ 15044547490712 := by decide +kernel

theorem rows22250R_5585 : rowsJ2 189 190 51 360 ≤ 2796567381026569 := by decide +kernel

theorem rows22250R_5586 : rowsJ2 190 191 0 36 ≤ 15554510877691 := by decide +kernel

theorem rows22250R_5587 : rowsJ2 190 191 36 38 ≤ 16994669330733 := by decide +kernel

theorem rows22250R_5588 : rowsJ2 190 191 38 40 ≤ 26323240635209 := by decide +kernel

theorem rows22250R_5589 : rowsJ2 190 191 40 41 ≤ 16076593482510 := by decide +kernel

theorem rows22250R_5590 : rowsJ2 190 191 41 42 ≤ 17747297158636 := by decide +kernel

theorem rows22250R_5591 : rowsJ2 190 191 42 43 ≤ 19478468261886 := by decide +kernel

theorem rows22250R_5592 : rowsJ2 190 191 43 44 ≤ 21268499194719 := by decide +kernel

theorem rows22250R_5593 : rowsJ2 190 191 44 45 ≤ 23116029799675 := by decide +kernel

theorem rows22250R_5594 : rowsJ2 190 191 45 46 ≤ 25019938669191 := by decide +kernel

theorem rows22250R_5595 : rowsJ2 190 191 46 47 ≤ 22633434120256 := by decide +kernel

theorem rows22250R_5596 : rowsJ2 190 191 47 48 ≤ 20389624181495 := by decide +kernel

theorem rows22250R_5597 : rowsJ2 190 191 48 49 ≤ 18283454853171 := by decide +kernel

theorem rows22250R_5598 : rowsJ2 190 191 49 50 ≤ 16310250769597 := by decide +kernel

theorem rows22250R_5599 : rowsJ2 190 191 50 360 ≤ 2920171726356619 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5584
#print axioms SieveCert.rows22250R_5599
