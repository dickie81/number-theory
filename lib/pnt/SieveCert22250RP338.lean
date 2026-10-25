/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4041–4055 of 5796

File 338 of 465: the parts `rows22250R_4041` … `rows22250R_4055` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 97739 tests: row 130 columns 94–95, row 130 columns 96–97, row 130 columns
98–359, row 131 columns 0–25, row 131 columns 26–28, row 131 columns 29–31, row 131 columns 32–35, row 131 columns
36–42, row 131 columns 43–58, row 131 columns 59–61, row 131 columns 62–63, row 131 columns 64–64, row 131 columns
65–65, row 131 columns 66–66, row 131 columns 67–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4041 : rowsJ2 130 131 94 96 ≤ 12856882170828 := by decide +kernel

theorem rows22250R_4042 : rowsJ2 130 131 96 98 ≤ 17781577020031 := by decide +kernel

theorem rows22250R_4043 : rowsJ2 130 131 98 360 ≤ 991962243753281 := by decide +kernel

theorem rows22250R_4044 : rowsJ2 131 132 0 26 ≤ 695324585221 := by decide +kernel

theorem rows22250R_4045 : rowsJ2 131 132 26 29 ≤ 7921372557546 := by decide +kernel

theorem rows22250R_4046 : rowsJ2 131 132 29 32 ≤ 15290602246170 := by decide +kernel

theorem rows22250R_4047 : rowsJ2 131 132 32 36 ≤ 11926310790990 := by decide +kernel

theorem rows22250R_4048 : rowsJ2 131 132 36 43 ≤ 4525301185120 := by decide +kernel

theorem rows22250R_4049 : rowsJ2 131 132 43 59 ≤ 1725011402368 := by decide +kernel

theorem rows22250R_4050 : rowsJ2 131 132 59 62 ≤ 3995821263510 := by decide +kernel

theorem rows22250R_4051 : rowsJ2 131 132 62 64 ≤ 4544482631180 := by decide +kernel

theorem rows22250R_4052 : rowsJ2 131 132 64 65 ≤ 2904035410292 := by decide +kernel

theorem rows22250R_4053 : rowsJ2 131 132 65 66 ≤ 3267378450000 := by decide +kernel

theorem rows22250R_4054 : rowsJ2 131 132 66 67 ≤ 3591436960280 := by decide +kernel

theorem rows22250R_4055 : rowsJ2 131 132 67 68 ≤ 3857614604610 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4041
#print axioms SieveCert.rows22250R_4055
