/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5293–5308 of 5796

File 433 of 465: the parts `rows22250R_5293` … `rows22250R_5308` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94173 tests: row 174 columns 56–56, row 174 columns 57–57, row 174 columns
58–58, row 174 columns 59–59, row 174 columns 60–60, row 174 columns 61–61, row 174 columns 62–63, row 174 columns
64–115, row 174 columns 116–359, row 175 columns 0–39, row 175 columns 40–42, row 175 columns 43–44, row 175 columns
45–45, row 175 columns 46–46, row 175 columns 47–47, row 175 columns 48–48), each a sum of refined costs (`rows2` or
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

theorem rows22250R_5293 : rowsJ2 174 175 56 57 ≤ 13395533648003 := by decide +kernel

theorem rows22250R_5294 : rowsJ2 174 175 57 58 ≤ 11959371676379 := by decide +kernel

theorem rows22250R_5295 : rowsJ2 174 175 58 59 ≤ 10614610565312 := by decide +kernel

theorem rows22250R_5296 : rowsJ2 174 175 59 60 ≤ 9358807125258 := by decide +kernel

theorem rows22250R_5297 : rowsJ2 174 175 60 61 ≤ 8189700535553 := by decide +kernel

theorem rows22250R_5298 : rowsJ2 174 175 61 62 ≤ 7105203998951 := by decide +kernel

theorem rows22250R_5299 : rowsJ2 174 175 62 64 ≤ 11285916744521 := by decide +kernel

theorem rows22250R_5300 : rowsJ2 174 175 64 116 ≤ 78158820886866 := by decide +kernel

theorem rows22250R_5301 : rowsJ2 174 175 116 360 ≤ 2461521658601109 := by decide +kernel

theorem rows22250R_5302 : rowsJ2 175 176 0 40 ≤ 8261797725854 := by decide +kernel

theorem rows22250R_5303 : rowsJ2 175 176 40 43 ≤ 15144311339911 := by decide +kernel

theorem rows22250R_5304 : rowsJ2 175 176 43 45 ≤ 14816657447415 := by decide +kernel

theorem rows22250R_5305 : rowsJ2 175 176 45 46 ≤ 8994891469380 := by decide +kernel

theorem rows22250R_5306 : rowsJ2 175 176 46 47 ≤ 10122895099814 := by decide +kernel

theorem rows22250R_5307 : rowsJ2 175 176 47 48 ≤ 11301113382022 := by decide +kernel

theorem rows22250R_5308 : rowsJ2 175 176 48 49 ≤ 12527768599794 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5293
#print axioms SieveCert.rows22250R_5308
