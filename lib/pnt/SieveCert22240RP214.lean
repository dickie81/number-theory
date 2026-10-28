/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2480–2493 of 5066

File 214 of 387: the parts `rows22240R_2480` … `rows22240R_2493` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 96021 in units of a depth-4 test: row 93 columns 92–92, row 93 columns
93–339, row 94 columns 0–15, row 94 columns 16–19, row 94 columns 20–24, row 94 columns 25–31, row 94 columns 32–35,
row 94 columns 36–37, row 94 columns 38–38, row 94 columns 39–39, row 94 columns 40–40, row 94 columns 41–41, row 94
columns 42–42, row 94 columns 43–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2480 : rowsJ2 93 94 92 93 ≤ 4323042030734 := by decide +kernel

theorem rows22240R_2481 : rowsJ2 93 94 93 340 ≤ 4487562130746 := by decide +kernel

theorem rows22240R_2482 : rowsJ2 94 95 0 16 ≤ 0 := by decide +kernel

theorem rows22240R_2483 : rowsJ2 94 95 16 20 ≤ 0 := by decide +kernel

theorem rows22240R_2484 : rowsJ2 94 95 20 25 ≤ 0 := by decide +kernel

theorem rows22240R_2485 : rowsJ2 94 95 25 32 ≤ 405941540305 := by decide +kernel

theorem rows22240R_2486 : rowsJ2 94 95 32 36 ≤ 9646477209445 := by decide +kernel

theorem rows22240R_2487 : rowsJ2 94 95 36 38 ≤ 12599750852511 := by decide +kernel

theorem rows22240R_2488 : rowsJ2 94 95 38 39 ≤ 8253674673258 := by decide +kernel

theorem rows22240R_2489 : rowsJ2 94 95 39 40 ≤ 9550778915565 := by decide +kernel

theorem rows22240R_2490 : rowsJ2 94 95 40 41 ≤ 10966830978344 := by decide +kernel

theorem rows22240R_2491 : rowsJ2 94 95 41 42 ≤ 12495938197622 := by decide +kernel

theorem rows22240R_2492 : rowsJ2 94 95 42 43 ≤ 14132711804246 := by decide +kernel

theorem rows22240R_2493 : rowsJ2 94 95 43 44 ≤ 15541269030733 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2480
#print axioms SieveCert.rows22240R_2493
