/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5250–5264 of 5796

File 430 of 465: the parts `rows22250R_5250` … `rows22250R_5264` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 93507 tests: row 172 columns 60–60, row 172 columns 61–61, row 172 columns
62–62, row 172 columns 63–64, row 172 columns 65–66, row 172 columns 67–359, row 173 columns 0–40, row 173 columns
41–43, row 173 columns 44–45, row 173 columns 46–46, row 173 columns 47–47, row 173 columns 48–48, row 173 columns
49–49, row 173 columns 50–50, row 173 columns 51–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_5250 : rowsJ2 172 173 60 61 ≤ 9029828897706 := by decide +kernel

theorem rows22250R_5251 : rowsJ2 172 173 61 62 ≤ 7902328067825 := by decide +kernel

theorem rows22250R_5252 : rowsJ2 172 173 62 63 ≤ 6856282256280 := by decide +kernel

theorem rows22250R_5253 : rowsJ2 172 173 63 65 ≤ 10891309468831 := by decide +kernel

theorem rows22250R_5254 : rowsJ2 172 173 65 67 ≤ 7641962448700 := by decide +kernel

theorem rows22250R_5255 : rowsJ2 172 173 67 360 ≤ 2527508456528714 := by decide +kernel

theorem rows22250R_5256 : rowsJ2 173 174 0 41 ≤ 8996553961854 := by decide +kernel

theorem rows22250R_5257 : rowsJ2 173 174 41 44 ≤ 14579740733946 := by decide +kernel

theorem rows22250R_5258 : rowsJ2 173 174 44 46 ≤ 14269637980622 := by decide +kernel

theorem rows22250R_5259 : rowsJ2 173 174 46 47 ≤ 8664580822963 := by decide +kernel

theorem rows22250R_5260 : rowsJ2 173 174 47 48 ≤ 9752426643592 := by decide +kernel

theorem rows22250R_5261 : rowsJ2 173 174 48 49 ≤ 10888855546896 := by decide +kernel

theorem rows22250R_5262 : rowsJ2 173 174 49 50 ≤ 12072146780373 := by decide +kernel

theorem rows22250R_5263 : rowsJ2 173 174 50 51 ≤ 13300748515400 := by decide +kernel

theorem rows22250R_5264 : rowsJ2 173 174 51 52 ≤ 14573269746731 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5250
#print axioms SieveCert.rows22250R_5264
