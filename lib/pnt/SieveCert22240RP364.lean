/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4678–4693 of 5066

File 364 of 387: the parts `rows22240R_4678` … `rows22240R_4693` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99212 in units of a depth-4 test: row 167 columns 56–56, row 167
columns 57–58, row 167 columns 59–109, row 167 columns 110–339, row 168 columns 0–37, row 168 columns 38–40, row 168
columns 41–42, row 168 columns 43–43, row 168 columns 44–44, row 168 columns 45–45, row 168 columns 46–46, row 168
columns 47–47, row 168 columns 48–48, row 168 columns 49–49, row 168 columns 50–50, row 168 columns 51–51), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4678 : rowsJ2 167 168 56 57 ≤ 9944236622060 := by decide +kernel

theorem rows22240R_4679 : rowsJ2 167 168 57 59 ≤ 15904172660088 := by decide +kernel

theorem rows22240R_4680 : rowsJ2 167 168 59 110 ≤ 324177270306807 := by decide +kernel

theorem rows22240R_4681 : rowsJ2 167 168 110 340 ≤ 2316244032375835 := by decide +kernel

theorem rows22240R_4682 : rowsJ2 168 169 0 38 ≤ 12468170011665 := by decide +kernel

theorem rows22240R_4683 : rowsJ2 168 169 38 41 ≤ 21397367441007 := by decide +kernel

theorem rows22240R_4684 : rowsJ2 168 169 41 43 ≤ 20523796488554 := by decide +kernel

theorem rows22240R_4685 : rowsJ2 168 169 43 44 ≤ 12349882995320 := by decide +kernel

theorem rows22240R_4686 : rowsJ2 168 169 44 45 ≤ 13828677485532 := by decide +kernel

theorem rows22240R_4687 : rowsJ2 168 169 45 46 ≤ 15369576782967 := by decide +kernel

theorem rows22240R_4688 : rowsJ2 168 169 46 47 ≤ 16970498839978 := by decide +kernel

theorem rows22240R_4689 : rowsJ2 168 169 47 48 ≤ 18629660977245 := by decide +kernel

theorem rows22240R_4690 : rowsJ2 168 169 48 49 ≤ 20345560271731 := by decide +kernel

theorem rows22240R_4691 : rowsJ2 168 169 49 50 ≤ 22116852837937 := by decide +kernel

theorem rows22240R_4692 : rowsJ2 168 169 50 51 ≤ 19924599885734 := by decide +kernel

theorem rows22240R_4693 : rowsJ2 168 169 51 52 ≤ 17866565493846 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4678
#print axioms SieveCert.rows22240R_4693
