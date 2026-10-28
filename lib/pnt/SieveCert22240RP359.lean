/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4601–4615 of 5066

File 359 of 387: the parts `rows22240R_4601` … `rows22240R_4615` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 98712 in units of a depth-4 test: row 163 columns 63–339, row 164
columns 0–39, row 164 columns 40–41, row 164 columns 42–43, row 164 columns 44–44, row 164 columns 45–45, row 164
columns 46–46, row 164 columns 47–47, row 164 columns 48–48, row 164 columns 49–49, row 164 columns 50–50, row 164
columns 51–51, row 164 columns 52–52, row 164 columns 53–53, row 164 columns 54–54), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4601 : rowsJ2 163 164 63 340 ≤ 2601324390824923 := by decide +kernel

theorem rows22240R_4602 : rowsJ2 164 165 0 40 ≤ 14162392532504 := by decide +kernel

theorem rows22240R_4603 : rowsJ2 164 165 40 42 ≤ 12066078899089 := by decide +kernel

theorem rows22240R_4604 : rowsJ2 164 165 42 44 ≤ 16514937813130 := by decide +kernel

theorem rows22240R_4605 : rowsJ2 164 165 44 45 ≤ 10094425126542 := by decide +kernel

theorem rows22240R_4606 : rowsJ2 164 165 45 46 ≤ 11403270741582 := by decide +kernel

theorem rows22240R_4607 : rowsJ2 164 165 46 47 ≤ 12772160758002 := by decide +kernel

theorem rows22240R_4608 : rowsJ2 164 165 47 48 ≤ 14198909232152 := by decide +kernel

theorem rows22240R_4609 : rowsJ2 164 165 48 49 ≤ 15681641245833 := by decide +kernel

theorem rows22240R_4610 : rowsJ2 164 165 49 50 ≤ 17218670786124 := by decide +kernel

theorem rows22240R_4611 : rowsJ2 164 165 50 51 ≤ 18808511206769 := by decide +kernel

theorem rows22240R_4612 : rowsJ2 164 165 51 52 ≤ 20449825924933 := by decide +kernel

theorem rows22240R_4613 : rowsJ2 164 165 52 53 ≤ 18427339185934 := by decide +kernel

theorem rows22240R_4614 : rowsJ2 164 165 53 54 ≤ 16527698465358 := by decide +kernel

theorem rows22240R_4615 : rowsJ2 164 165 54 55 ≤ 14746957934152 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4601
#print axioms SieveCert.rows22240R_4615
