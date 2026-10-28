/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4061–4076 of 4715

File 310 of 351: the parts `rows22250R_4061` … `rows22250R_4076` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 95093 in units of a depth-4 test: row 153 columns 60–60, row 153
columns 61–61, row 153 columns 62–62, row 153 columns 63–63, row 153 columns 64–65, row 153 columns 66–68, row 153
columns 69–129, row 153 columns 130–339, row 154 columns 0–42, row 154 columns 43–45, row 154 columns 46–47, row 154
columns 48–48, row 154 columns 49–49, row 154 columns 50–50, row 154 columns 51–51, row 154 columns 52–52), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4061 : rowsJ2 153 154 60 61 ≤ 9620890552825 := by decide +kernel

theorem rows22250R_4062 : rowsJ2 153 154 61 62 ≤ 8417586754848 := by decide +kernel

theorem rows22250R_4063 : rowsJ2 153 154 62 63 ≤ 7301621998719 := by decide +kernel

theorem rows22250R_4064 : rowsJ2 153 154 63 64 ≤ 6270988997325 := by decide +kernel

theorem rows22250R_4065 : rowsJ2 153 154 64 66 ≤ 9782345541662 := by decide +kernel

theorem rows22250R_4066 : rowsJ2 153 154 66 69 ≤ 8979326836807 := by decide +kernel

theorem rows22250R_4067 : rowsJ2 153 154 69 130 ≤ 719724852484205 := by decide +kernel

theorem rows22250R_4068 : rowsJ2 153 154 130 340 ≤ 1645327935593033 := by decide +kernel

theorem rows22250R_4069 : rowsJ2 154 155 0 43 ≤ 8284803536159 := by decide +kernel

theorem rows22250R_4070 : rowsJ2 154 155 43 46 ≤ 12574405494899 := by decide +kernel

theorem rows22250R_4071 : rowsJ2 154 155 46 48 ≤ 12792725771716 := by decide +kernel

theorem rows22250R_4072 : rowsJ2 154 155 48 49 ≤ 7897898178126 := by decide +kernel

theorem rows22250R_4073 : rowsJ2 154 155 49 50 ≤ 8972361889165 := by decide +kernel

theorem rows22250R_4074 : rowsJ2 154 155 50 51 ≤ 10099152965122 := by decide +kernel

theorem rows22250R_4075 : rowsJ2 154 155 51 52 ≤ 11276304094202 := by decide +kernel

theorem rows22250R_4076 : rowsJ2 154 155 52 53 ≤ 12502031502346 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4061
#print axioms SieveCert.rows22250R_4076
