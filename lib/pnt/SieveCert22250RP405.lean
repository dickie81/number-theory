/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4914–4924 of 5796

File 405 of 465: the parts `rows22250R_4914` … `rows22250R_4924` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 99190 tests: row 159 columns 58–58, row 159 columns 59–59, row 159 columns
60–60, row 159 columns 61–61, row 159 columns 62–62, row 159 columns 63–63, row 159 columns 64–64, row 159 columns
65–65, row 159 columns 66–66, row 159 columns 67–67, row 159 columns 68–68), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4914 : rowsJ2 159 160 58 59 ≤ 11448709922012 := by decide +kernel

theorem rows22250R_4915 : rowsJ2 159 160 59 60 ≤ 12489783831557 := by decide +kernel

theorem rows22250R_4916 : rowsJ2 159 160 60 61 ≤ 13564256756099 := by decide +kernel

theorem rows22250R_4917 : rowsJ2 159 160 61 62 ≤ 13441834277698 := by decide +kernel

theorem rows22250R_4918 : rowsJ2 159 160 62 63 ≤ 12154633807544 := by decide +kernel

theorem rows22250R_4919 : rowsJ2 159 160 63 64 ≤ 10941225991369 := by decide +kernel

theorem rows22250R_4920 : rowsJ2 159 160 64 65 ≤ 9799664764217 := by decide +kernel

theorem rows22250R_4921 : rowsJ2 159 160 65 66 ≤ 8728133821161 := by decide +kernel

theorem rows22250R_4922 : rowsJ2 159 160 66 67 ≤ 7724940740494 := by decide +kernel

theorem rows22250R_4923 : rowsJ2 159 160 67 68 ≤ 6788511612236 := by decide +kernel

theorem rows22250R_4924 : rowsJ2 159 160 68 69 ≤ 5917386138213 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4914
#print axioms SieveCert.rows22250R_4924
