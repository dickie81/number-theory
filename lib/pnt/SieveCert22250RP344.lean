/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4600–4616 of 4715

File 344 of 351: the parts `rows22250R_4600` … `rows22250R_4616` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 97115 tests: row 185 columns 38–38, row 185 columns 39–39, row 185 columns
40–40, row 185 columns 41–41, row 185 columns 42–339, row 186 columns 0–31, row 186 columns 32–34, row 186 columns
35–36, row 186 columns 37–37, row 186 columns 38–38, row 186 columns 39–39, row 186 columns 40–40, row 186 columns
41–339, row 187 columns 0–31, row 187 columns 32–33, row 187 columns 34–35, row 187 columns 36–36), each a sum of
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

theorem rows22250R_4600 : rowsJ2 185 186 38 39 ≤ 27210893984712 := by decide +kernel

theorem rows22250R_4601 : rowsJ2 185 186 39 40 ≤ 29691960646002 := by decide +kernel

theorem rows22250R_4602 : rowsJ2 185 186 40 41 ≤ 29350799800649 := by decide +kernel

theorem rows22250R_4603 : rowsJ2 185 186 41 42 ≤ 26283588616535 := by decide +kernel

theorem rows22250R_4604 : rowsJ2 185 186 42 340 ≤ 3860926322243901 := by decide +kernel

theorem rows22250R_4605 : rowsJ2 186 187 0 32 ≤ 21626507269085 := by decide +kernel

theorem rows22250R_4606 : rowsJ2 186 187 32 35 ≤ 40165163206182 := by decide +kernel

theorem rows22250R_4607 : rowsJ2 186 187 35 37 ≤ 44359795954714 := by decide +kernel

theorem rows22250R_4608 : rowsJ2 186 187 37 38 ≤ 26599222624742 := by decide +kernel

theorem rows22250R_4609 : rowsJ2 186 187 38 39 ≤ 29097027332392 := by decide +kernel

theorem rows22250R_4610 : rowsJ2 186 187 39 40 ≤ 31676972991837 := by decide +kernel

theorem rows22250R_4611 : rowsJ2 186 187 40 41 ≤ 28428377217994 := by decide +kernel

theorem rows22250R_4612 : rowsJ2 186 187 41 340 ≤ 3992439759930506 := by decide +kernel

theorem rows22250R_4613 : rowsJ2 187 188 0 32 ≤ 25123661927760 := by decide +kernel

theorem rows22250R_4614 : rowsJ2 187 188 32 34 ≤ 25984905037944 := by decide +kernel

theorem rows22250R_4615 : rowsJ2 187 188 34 36 ≤ 39725954911208 := by decide +kernel

theorem rows22250R_4616 : rowsJ2 187 188 36 37 ≤ 26016842591349 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4600
#print axioms SieveCert.rows22250R_4616
