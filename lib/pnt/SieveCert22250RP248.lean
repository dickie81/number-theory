/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3167–3181 of 4715

File 248 of 351: the parts `rows22250R_3167` … `rows22250R_3181` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99355 tests: row 118 columns 92–93, row 118 columns 94–102, row 118 columns
103–339, row 119 columns 0–25, row 119 columns 26–28, row 119 columns 29–30, row 119 columns 31–33, row 119 columns
34–37, row 119 columns 38–46, row 119 columns 47–58, row 119 columns 59–61, row 119 columns 62–63, row 119 columns
64–65, row 119 columns 66–67, row 119 columns 68–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3167 : rowsJ2 118 119 92 94 ≤ 18942192237231 := by decide +kernel

theorem rows22250R_3168 : rowsJ2 118 119 94 103 ≤ 715870784467834 := by decide +kernel

theorem rows22250R_3169 : rowsJ2 118 119 103 340 ≤ 639912714645291 := by decide +kernel

theorem rows22250R_3170 : rowsJ2 119 120 0 26 ≤ 1331893499504 := by decide +kernel

theorem rows22250R_3171 : rowsJ2 119 120 26 29 ≤ 10624630316586 := by decide +kernel

theorem rows22250R_3172 : rowsJ2 119 120 29 31 ≤ 15511457267238 := by decide +kernel

theorem rows22250R_3173 : rowsJ2 119 120 31 34 ≤ 20240778880772 := by decide +kernel

theorem rows22250R_3174 : rowsJ2 119 120 34 38 ≤ 15338569740519 := by decide +kernel

theorem rows22250R_3175 : rowsJ2 119 120 38 47 ≤ 3624432775389 := by decide +kernel

theorem rows22250R_3176 : rowsJ2 119 120 47 59 ≤ 2605077945441 := by decide +kernel

theorem rows22250R_3177 : rowsJ2 119 120 59 62 ≤ 5116609380804 := by decide +kernel

theorem rows22250R_3178 : rowsJ2 119 120 62 64 ≤ 4751113856951 := by decide +kernel

theorem rows22250R_3179 : rowsJ2 119 120 64 66 ≤ 5236100852774 := by decide +kernel

theorem rows22250R_3180 : rowsJ2 119 120 66 68 ≤ 5199128697780 := by decide +kernel

theorem rows22250R_3181 : rowsJ2 119 120 68 70 ≤ 4619282103608 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3167
#print axioms SieveCert.rows22250R_3181
