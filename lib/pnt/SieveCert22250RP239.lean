/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3034–3047 of 4715

File 239 of 351: the parts `rows22250R_3034` … `rows22250R_3047` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 97887 tests: row 113 columns 0–26, row 113 columns 27–30, row 113 columns
31–32, row 113 columns 33–34, row 113 columns 35–36, row 113 columns 37–39, row 113 columns 40–43, row 113 columns
44–52, row 113 columns 53–61, row 113 columns 62–65, row 113 columns 66–69, row 113 columns 70–73, row 113 columns
74–76, row 113 columns 77–79), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_3034 : rowsJ2 113 114 0 27 ≤ 1060800789168 := by decide +kernel

theorem rows22250R_3035 : rowsJ2 113 114 27 31 ≤ 12923216986696 := by decide +kernel

theorem rows22250R_3036 : rowsJ2 113 114 31 33 ≤ 16470355490269 := by decide +kernel

theorem rows22250R_3037 : rowsJ2 113 114 33 35 ≤ 22452175667853 := by decide +kernel

theorem rows22250R_3038 : rowsJ2 113 114 35 37 ≤ 18085632919599 := by decide +kernel

theorem rows22250R_3039 : rowsJ2 113 114 37 40 ≤ 18040454054382 := by decide +kernel

theorem rows22250R_3040 : rowsJ2 113 114 40 44 ≤ 8502535696654 := by decide +kernel

theorem rows22250R_3041 : rowsJ2 113 114 44 53 ≤ 1115454326249 := by decide +kernel

theorem rows22250R_3042 : rowsJ2 113 114 53 62 ≤ 2237622276369 := by decide +kernel

theorem rows22250R_3043 : rowsJ2 113 114 62 66 ≤ 3368803197792 := by decide +kernel

theorem rows22250R_3044 : rowsJ2 113 114 66 70 ≤ 887248657874 := by decide +kernel

theorem rows22250R_3045 : rowsJ2 113 114 70 74 ≤ 0 := by decide +kernel

theorem rows22250R_3046 : rowsJ2 113 114 74 77 ≤ 42834464512 := by decide +kernel

theorem rows22250R_3047 : rowsJ2 113 114 77 80 ≤ 14398040078 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3034
#print axioms SieveCert.rows22250R_3047
