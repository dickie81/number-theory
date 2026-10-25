/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4941–4951 of 5796

File 407 of 465: the parts `rows22250R_4941` … `rows22250R_4951` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 99856 tests: row 160 columns 57–57, row 160 columns 58–58, row 160 columns
59–59, row 160 columns 60–60, row 160 columns 61–61, row 160 columns 62–62, row 160 columns 63–63, row 160 columns
64–64, row 160 columns 65–65, row 160 columns 66–66, row 160 columns 67–67), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4941 : rowsJ2 160 161 57 58 ≤ 11129808125096 := by decide +kernel

theorem rows22250R_4942 : rowsJ2 160 161 58 59 ≤ 12170074055791 := by decide +kernel

theorem rows22250R_4943 : rowsJ2 160 161 59 60 ≤ 13244695290472 := by decide +kernel

theorem rows22250R_4944 : rowsJ2 160 161 60 61 ≤ 14352774706077 := by decide +kernel

theorem rows22250R_4945 : rowsJ2 160 161 61 62 ≤ 13005618656584 := by decide +kernel

theorem rows22250R_4946 : rowsJ2 160 161 62 63 ≤ 11734646118096 := by decide +kernel

theorem rows22250R_4947 : rowsJ2 160 161 63 64 ≤ 10537790458849 := by decide +kernel

theorem rows22250R_4948 : rowsJ2 160 161 64 65 ≤ 9413121943408 := by decide +kernel

theorem rows22250R_4949 : rowsJ2 160 161 65 66 ≤ 8358841353311 := by decide +kernel

theorem rows22250R_4950 : rowsJ2 160 161 66 67 ≤ 7373274153745 := by decide +kernel

theorem rows22250R_4951 : rowsJ2 160 161 67 68 ≤ 6454865168818 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4941
#print axioms SieveCert.rows22250R_4951
