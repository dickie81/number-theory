/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4541–4554 of 5066

File 355 of 387: the parts `rows22240R_4541` … `rows22240R_4554` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 97821 in units of a depth-4 test: row 161 columns 41–43, row 161
columns 44–45, row 161 columns 46–46, row 161 columns 47–47, row 161 columns 48–48, row 161 columns 49–49, row 161
columns 50–50, row 161 columns 51–51, row 161 columns 52–52, row 161 columns 53–53, row 161 columns 54–54, row 161
columns 55–55, row 161 columns 56–56, row 161 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4541 : rowsJ2 161 162 41 44 ≤ 17063449852143 := by decide +kernel

theorem rows22240R_4542 : rowsJ2 161 162 44 46 ≤ 16680405961842 := by decide +kernel

theorem rows22240R_4543 : rowsJ2 161 162 46 47 ≤ 10121744445180 := by decide +kernel

theorem rows22240R_4544 : rowsJ2 161 162 47 48 ≤ 11387797749446 := by decide +kernel

theorem rows22240R_4545 : rowsJ2 161 162 48 49 ≤ 12709851992820 := by decide +kernel

theorem rows22240R_4546 : rowsJ2 161 162 49 50 ≤ 14086018345510 := by decide +kernel

theorem rows22240R_4547 : rowsJ2 161 162 50 51 ≤ 15514575647933 := by decide +kernel

theorem rows22240R_4548 : rowsJ2 161 162 51 52 ≤ 16993961107225 := by decide +kernel

theorem rows22240R_4549 : rowsJ2 161 162 52 53 ≤ 18522782105970 := by decide +kernel

theorem rows22240R_4550 : rowsJ2 161 162 53 54 ≤ 18337019386704 := by decide +kernel

theorem rows22240R_4551 : rowsJ2 161 162 54 55 ≤ 16487709555642 := by decide +kernel

theorem rows22240R_4552 : rowsJ2 161 162 55 56 ≤ 14751777933919 := by decide +kernel

theorem rows22240R_4553 : rowsJ2 161 162 56 57 ≤ 13125756024013 := by decide +kernel

theorem rows22240R_4554 : rowsJ2 161 162 57 58 ≤ 11606429835996 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4541
#print axioms SieveCert.rows22240R_4554
