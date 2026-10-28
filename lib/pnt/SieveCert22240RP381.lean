/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4958–4973 of 5066

File 381 of 387: the parts `rows22240R_4958` … `rows22240R_4973` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99403 in units of a depth-4 test: row 187 columns 0–31, row 187 columns
32–34, row 187 columns 35–36, row 187 columns 37–37, row 187 columns 38–38, row 187 columns 39–39, row 187 columns
40–40, row 187 columns 41–339, row 188 columns 0–31, row 188 columns 32–34, row 188 columns 35–36, row 188 columns
37–37, row 188 columns 38–38, row 188 columns 39–39, row 188 columns 40–339, row 189 columns 0–31), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4958 : rowsJ2 187 188 0 32 ≤ 18613534648697 := by decide +kernel

theorem rows22240R_4959 : rowsJ2 187 188 32 35 ≤ 36970774282514 := by decide +kernel

theorem rows22240R_4960 : rowsJ2 187 188 35 37 ≤ 41487205267214 := by decide +kernel

theorem rows22240R_4961 : rowsJ2 187 188 37 38 ≤ 26953935340966 := by decide +kernel

theorem rows22240R_4962 : rowsJ2 187 188 38 39 ≤ 29483869365639 := by decide +kernel

theorem rows22240R_4963 : rowsJ2 187 188 39 40 ≤ 32097015924678 := by decide +kernel

theorem rows22240R_4964 : rowsJ2 187 188 40 41 ≤ 31726545047132 := by decide +kernel

theorem rows22240R_4965 : rowsJ2 187 188 41 340 ≤ 4083774683941059 := by decide +kernel

theorem rows22240R_4966 : rowsJ2 188 189 0 32 ≤ 21816314028813 := by decide +kernel

theorem rows22240R_4967 : rowsJ2 188 189 32 35 ≤ 40521506281272 := by decide +kernel

theorem rows22240R_4968 : rowsJ2 188 189 35 37 ≤ 44760194440091 := by decide +kernel

theorem rows22240R_4969 : rowsJ2 188 189 37 38 ≤ 28915336826331 := by decide +kernel

theorem rows22240R_4970 : rowsJ2 188 189 38 39 ≤ 31547678389822 := by decide +kernel

theorem rows22240R_4971 : rowsJ2 188 189 39 40 ≤ 34124121826951 := by decide +kernel

theorem rows22240R_4972 : rowsJ2 188 189 40 340 ≤ 4217228901541706 := by decide +kernel

theorem rows22240R_4973 : rowsJ2 189 190 0 32 ≤ 25347585945341 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4958
#print axioms SieveCert.rows22240R_4973
