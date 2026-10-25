/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3189–3204 of 5796

File 284 of 465: the parts `rows22250R_3189` … `rows22250R_3204` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94468 tests: row 107 columns 36–37, row 107 columns 38–38, row 107 columns
39–39, row 107 columns 40–40, row 107 columns 41–41, row 107 columns 42–42, row 107 columns 43–43, row 107 columns
44–44, row 107 columns 45–45, row 107 columns 46–46, row 107 columns 47–47, row 107 columns 48–48, row 107 columns
49–50, row 107 columns 51–52, row 107 columns 53–54, row 107 columns 55–57), each a sum of refined costs (`rows2` or
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

theorem rows22250R_3189 : rowsJ2 107 108 36 38 ≤ 12624845712473 := by decide +kernel

theorem rows22250R_3190 : rowsJ2 107 108 38 39 ≤ 8996160517427 := by decide +kernel

theorem rows22250R_3191 : rowsJ2 107 108 39 40 ≤ 10918458051141 := by decide +kernel

theorem rows22250R_3192 : rowsJ2 107 108 40 41 ≤ 12220778301319 := by decide +kernel

theorem rows22250R_3193 : rowsJ2 107 108 41 42 ≤ 13529242851833 := by decide +kernel

theorem rows22250R_3194 : rowsJ2 107 108 42 43 ≤ 13332072348485 := by decide +kernel

theorem rows22250R_3195 : rowsJ2 107 108 43 44 ≤ 11825704687074 := by decide +kernel

theorem rows22250R_3196 : rowsJ2 107 108 44 45 ≤ 10336442894559 := by decide +kernel

theorem rows22250R_3197 : rowsJ2 107 108 45 46 ≤ 8913816591491 := by decide +kernel

theorem rows22250R_3198 : rowsJ2 107 108 46 47 ≤ 7557675487921 := by decide +kernel

theorem rows22250R_3199 : rowsJ2 107 108 47 48 ≤ 6267981047854 := by decide +kernel

theorem rows22250R_3200 : rowsJ2 107 108 48 49 ≤ 5128506162344 := by decide +kernel

theorem rows22250R_3201 : rowsJ2 107 108 49 51 ≤ 7426031254550 := by decide +kernel

theorem rows22250R_3202 : rowsJ2 107 108 51 53 ≤ 4532529349580 := by decide +kernel

theorem rows22250R_3203 : rowsJ2 107 108 53 55 ≤ 2245715982203 := by decide +kernel

theorem rows22250R_3204 : rowsJ2 107 108 55 58 ≤ 579303712365 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3189
#print axioms SieveCert.rows22250R_3204
