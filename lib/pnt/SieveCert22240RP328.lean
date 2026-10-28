/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4157–4169 of 5066

File 328 of 387: the parts `rows22240R_4157` … `rows22240R_4169` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 95083 in units of a depth-4 test: row 145 columns 28–47, row 145
columns 48–49, row 145 columns 50–51, row 145 columns 52–52, row 145 columns 53–53, row 145 columns 54–54, row 145
columns 55–55, row 145 columns 56–56, row 145 columns 57–57, row 145 columns 58–58, row 145 columns 59–59, row 145
columns 60–60, row 145 columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4157 : rowsJ2 145 146 28 48 ≤ 6983871782429 := by decide +kernel

theorem rows22240R_4158 : rowsJ2 145 146 48 50 ≤ 6391978449812 := by decide +kernel

theorem rows22240R_4159 : rowsJ2 145 146 50 52 ≤ 9247359323557 := by decide +kernel

theorem rows22240R_4160 : rowsJ2 145 146 52 53 ≤ 5827236784950 := by decide +kernel

theorem rows22240R_4161 : rowsJ2 145 146 53 54 ≤ 6695973878829 := by decide +kernel

theorem rows22240R_4162 : rowsJ2 145 146 54 55 ≤ 7611960128921 := by decide +kernel

theorem rows22240R_4163 : rowsJ2 145 146 55 56 ≤ 8573352897158 := by decide +kernel

theorem rows22240R_4164 : rowsJ2 145 146 56 57 ≤ 9578446250529 := by decide +kernel

theorem rows22240R_4165 : rowsJ2 145 146 57 58 ≤ 10625646153392 := by decide +kernel

theorem rows22240R_4166 : rowsJ2 145 146 58 59 ≤ 11713465412693 := by decide +kernel

theorem rows22240R_4167 : rowsJ2 145 146 59 60 ≤ 12840526598254 := by decide +kernel

theorem rows22240R_4168 : rowsJ2 145 146 60 61 ≤ 14005549497415 := by decide +kernel

theorem rows22240R_4169 : rowsJ2 145 146 61 62 ≤ 13875517724412 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4157
#print axioms SieveCert.rows22240R_4169
