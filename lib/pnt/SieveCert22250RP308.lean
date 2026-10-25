/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4033–4046 of 4715

File 308 of 351: the parts `rows22250R_4033` … `rows22250R_4046` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 99150 tests: row 152 columns 55–55, row 152 columns 56–56, row 152 columns
57–57, row 152 columns 58–58, row 152 columns 59–59, row 152 columns 60–60, row 152 columns 61–61, row 152 columns
62–62, row 152 columns 63–63, row 152 columns 64–65, row 152 columns 66–67, row 152 columns 68–71, row 152 columns
72–339, row 153 columns 0–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_4033 : rowsJ2 152 153 55 56 ≤ 14572024990368 := by decide +kernel

theorem rows22250R_4034 : rowsJ2 152 153 56 57 ≤ 15888909541130 := by decide +kernel

theorem rows22250R_4035 : rowsJ2 152 153 57 58 ≤ 14291880333346 := by decide +kernel

theorem rows22250R_4036 : rowsJ2 152 153 58 59 ≤ 12791557412975 := by decide +kernel

theorem rows22250R_4037 : rowsJ2 152 153 59 60 ≤ 11385176787224 := by decide +kernel

theorem rows22250R_4038 : rowsJ2 152 153 60 61 ≤ 10070169893058 := by decide +kernel

theorem rows22250R_4039 : rowsJ2 152 153 61 62 ≤ 8844154039159 := by decide +kernel

theorem rows22250R_4040 : rowsJ2 152 153 62 63 ≤ 7704923720185 := by decide +kernel

theorem rows22250R_4041 : rowsJ2 152 153 63 64 ≤ 6650442740773 := by decide +kernel

theorem rows22250R_4042 : rowsJ2 152 153 64 66 ≤ 10467225640041 := by decide +kernel

theorem rows22250R_4043 : rowsJ2 152 153 66 68 ≤ 7222363654741 := by decide +kernel

theorem rows22250R_4044 : rowsJ2 152 153 68 72 ≤ 7173645546803 := by decide +kernel

theorem rows22250R_4045 : rowsJ2 152 153 72 340 ≤ 2241489431864312 := by decide +kernel

theorem rows22250R_4046 : rowsJ2 153 154 0 43 ≤ 6828267232484 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4033
#print axioms SieveCert.rows22250R_4046
