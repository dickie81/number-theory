/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4025–4036 of 5066

File 318 of 387: the parts `rows22240R_4025` … `rows22240R_4036` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 94443 in units of a depth-4 test: row 140 columns 52–53, row 140
columns 54–54, row 140 columns 55–55, row 140 columns 56–56, row 140 columns 57–57, row 140 columns 58–58, row 140
columns 59–59, row 140 columns 60–60, row 140 columns 61–61, row 140 columns 62–62, row 140 columns 63–63, row 140
columns 64–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4025 : rowsJ2 140 141 52 54 ≤ 7840000617591 := by decide +kernel

theorem rows22240R_4026 : rowsJ2 140 141 54 55 ≤ 4995492968621 := by decide +kernel

theorem rows22240R_4027 : rowsJ2 140 141 55 56 ≤ 5775573113139 := by decide +kernel

theorem rows22240R_4028 : rowsJ2 140 141 56 57 ≤ 6600545011007 := by decide +kernel

theorem rows22240R_4029 : rowsJ2 140 141 57 58 ≤ 7468609455326 := by decide +kernel

theorem rows22240R_4030 : rowsJ2 140 141 58 59 ≤ 8378094327497 := by decide +kernel

theorem rows22240R_4031 : rowsJ2 140 141 59 60 ≤ 9327419003886 := by decide +kernel

theorem rows22240R_4032 : rowsJ2 140 141 60 61 ≤ 10315119284512 := by decide +kernel

theorem rows22240R_4033 : rowsJ2 140 141 61 62 ≤ 11319856596059 := by decide +kernel

theorem rows22240R_4034 : rowsJ2 140 141 62 63 ≤ 12281202749706 := by decide +kernel

theorem rows22240R_4035 : rowsJ2 140 141 63 64 ≤ 13178876647389 := by decide +kernel

theorem rows22240R_4036 : rowsJ2 140 141 64 65 ≤ 11936763202164 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4025
#print axioms SieveCert.rows22240R_4036
