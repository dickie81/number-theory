/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2499–2511 of 5796

File 230 of 465: the parts `rows22250R_2499` … `rows22250R_2511` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 95803 tests: row 92 columns 92–359, row 93 columns 0–16, row 93 columns
17–19, row 93 columns 20–22, row 93 columns 23–26, row 93 columns 27–32, row 93 columns 33–36, row 93 columns 37–38,
row 93 columns 39–40, row 93 columns 41–41, row 93 columns 42–42, row 93 columns 43–43, row 93 columns 44–44), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22250R_2499 : rowsJ2 92 93 92 360 ≤ 6629957754115 := by decide +kernel

theorem rows22250R_2500 : rowsJ2 93 94 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_2501 : rowsJ2 93 94 17 20 ≤ 0 := by decide +kernel

theorem rows22250R_2502 : rowsJ2 93 94 20 23 ≤ 0 := by decide +kernel

theorem rows22250R_2503 : rowsJ2 93 94 23 27 ≤ 0 := by decide +kernel

theorem rows22250R_2504 : rowsJ2 93 94 27 33 ≤ 0 := by decide +kernel

theorem rows22250R_2505 : rowsJ2 93 94 33 37 ≤ 2773522566570 := by decide +kernel

theorem rows22250R_2506 : rowsJ2 93 94 37 39 ≤ 5737315588170 := by decide +kernel

theorem rows22250R_2507 : rowsJ2 93 94 39 41 ≤ 9941851605724 := by decide +kernel

theorem rows22250R_2508 : rowsJ2 93 94 41 42 ≤ 6419984426703 := by decide +kernel

theorem rows22250R_2509 : rowsJ2 93 94 42 43 ≤ 7520227106961 := by decide +kernel

theorem rows22250R_2510 : rowsJ2 93 94 43 44 ≤ 8715050691457 := by decide +kernel

theorem rows22250R_2511 : rowsJ2 93 94 44 45 ≤ 9919476200542 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2499
#print axioms SieveCert.rows22250R_2511
