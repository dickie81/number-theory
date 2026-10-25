/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2315–2330 of 4715

File 192 of 351: the parts `rows22250R_2315` … `rows22250R_2330` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 95197 tests: row 93 columns 39–39, row 93 columns 40–40, row 93 columns
41–41, row 93 columns 42–42, row 93 columns 43–43, row 93 columns 44–44, row 93 columns 45–45, row 93 columns 46–46,
row 93 columns 47–47, row 93 columns 48–48, row 93 columns 49–49, row 93 columns 50–50, row 93 columns 51–51, row 93
columns 52–53, row 93 columns 54–55, row 93 columns 56–57), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2315 : rowsJ2 93 94 39 40 ≤ 10798864555776 := by decide +kernel

theorem rows22250R_2316 : rowsJ2 93 94 40 41 ≤ 12397292574415 := by decide +kernel

theorem rows22250R_2317 : rowsJ2 93 94 41 42 ≤ 14000311021419 := by decide +kernel

theorem rows22250R_2318 : rowsJ2 93 94 42 43 ≤ 15489049125762 := by decide +kernel

theorem rows22250R_2319 : rowsJ2 93 94 43 44 ≤ 16688884152219 := by decide +kernel

theorem rows22250R_2320 : rowsJ2 93 94 44 45 ≤ 14911615580103 := by decide +kernel

theorem rows22250R_2321 : rowsJ2 93 94 45 46 ≤ 13155238523412 := by decide +kernel

theorem rows22250R_2322 : rowsJ2 93 94 46 47 ≤ 11478365389530 := by decide +kernel

theorem rows22250R_2323 : rowsJ2 93 94 47 48 ≤ 9819695317866 := by decide +kernel

theorem rows22250R_2324 : rowsJ2 93 94 48 49 ≤ 8337246947348 := by decide +kernel

theorem rows22250R_2325 : rowsJ2 93 94 49 50 ≤ 6965362194019 := by decide +kernel

theorem rows22250R_2326 : rowsJ2 93 94 50 51 ≤ 4556809860745 := by decide +kernel

theorem rows22250R_2327 : rowsJ2 93 94 51 52 ≤ 2542696594509 := by decide +kernel

theorem rows22250R_2328 : rowsJ2 93 94 52 54 ≤ 1149519839424 := by decide +kernel

theorem rows22250R_2329 : rowsJ2 93 94 54 56 ≤ 0 := by decide +kernel

theorem rows22250R_2330 : rowsJ2 93 94 56 58 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2315
#print axioms SieveCert.rows22250R_2330
