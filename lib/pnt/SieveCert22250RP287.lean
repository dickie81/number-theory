/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3236–3251 of 5796

File 287 of 465: the parts `rows22250R_3236` … `rows22250R_3251` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 95061 tests: row 108 columns 18–30, row 108 columns 31–34, row 108 columns
35–36, row 108 columns 37–37, row 108 columns 38–38, row 108 columns 39–39, row 108 columns 40–40, row 108 columns
41–41, row 108 columns 42–42, row 108 columns 43–43, row 108 columns 44–44, row 108 columns 45–45, row 108 columns
46–46, row 108 columns 47–47, row 108 columns 48–49, row 108 columns 50–51), each a sum of refined costs (`rows2` or
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

theorem rows22250R_3236 : rowsJ2 108 109 18 31 ≤ 522641162800 := by decide +kernel

theorem rows22250R_3237 : rowsJ2 108 109 31 35 ≤ 7770177090616 := by decide +kernel

theorem rows22250R_3238 : rowsJ2 108 109 35 37 ≤ 10557970422967 := by decide +kernel

theorem rows22250R_3239 : rowsJ2 108 109 37 38 ≤ 7656910072313 := by decide +kernel

theorem rows22250R_3240 : rowsJ2 108 109 38 39 ≤ 9563503293491 := by decide +kernel

theorem rows22250R_3241 : rowsJ2 108 109 39 40 ≤ 11474216271643 := by decide +kernel

theorem rows22250R_3242 : rowsJ2 108 109 40 41 ≤ 12761324018730 := by decide +kernel

theorem rows22250R_3243 : rowsJ2 108 109 41 42 ≤ 14091795683207 := by decide +kernel

theorem rows22250R_3244 : rowsJ2 108 109 42 43 ≤ 12483295724151 := by decide +kernel

theorem rows22250R_3245 : rowsJ2 108 109 43 44 ≤ 10979631286261 := by decide +kernel

theorem rows22250R_3246 : rowsJ2 108 109 44 45 ≤ 9543394293862 := by decide +kernel

theorem rows22250R_3247 : rowsJ2 108 109 45 46 ≤ 8174395408403 := by decide +kernel

theorem rows22250R_3248 : rowsJ2 108 109 46 47 ≤ 6872559166371 := by decide +kernel

theorem rows22250R_3249 : rowsJ2 108 109 47 48 ≤ 5637924817933 := by decide +kernel

theorem rows22250R_3250 : rowsJ2 108 109 48 50 ≤ 8175312897884 := by decide +kernel

theorem rows22250R_3251 : rowsJ2 108 109 50 52 ≤ 5022214645228 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3236
#print axioms SieveCert.rows22250R_3251
