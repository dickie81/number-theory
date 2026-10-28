/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2571–2583 of 5066

File 221 of 387: the parts `rows22240R_2571` … `rows22240R_2583` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 92796 in units of a depth-4 test: row 95 columns 93–93, row 95 columns
94–94, row 95 columns 95–339, row 96 columns 0–15, row 96 columns 16–20, row 96 columns 21–28, row 96 columns 29–33,
row 96 columns 34–36, row 96 columns 37–38, row 96 columns 39–39, row 96 columns 40–40, row 96 columns 41–41, row 96
columns 42–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2571 : rowsJ2 95 96 93 94 ≤ 4095509236161 := by decide +kernel

theorem rows22240R_2572 : rowsJ2 95 96 94 95 ≤ 4478428029676 := by decide +kernel

theorem rows22240R_2573 : rowsJ2 95 96 95 340 ≤ 4900950303725 := by decide +kernel

theorem rows22240R_2574 : rowsJ2 96 97 0 16 ≤ 0 := by decide +kernel

theorem rows22240R_2575 : rowsJ2 96 97 16 21 ≤ 0 := by decide +kernel

theorem rows22240R_2576 : rowsJ2 96 97 21 29 ≤ 0 := by decide +kernel

theorem rows22240R_2577 : rowsJ2 96 97 29 34 ≤ 4588149196676 := by decide +kernel

theorem rows22240R_2578 : rowsJ2 96 97 34 37 ≤ 14314230827877 := by decide +kernel

theorem rows22240R_2579 : rowsJ2 96 97 37 39 ≤ 17196152940664 := by decide +kernel

theorem rows22240R_2580 : rowsJ2 96 97 39 40 ≤ 10746315673910 := by decide +kernel

theorem rows22240R_2581 : rowsJ2 96 97 40 41 ≤ 12335870524540 := by decide +kernel

theorem rows22240R_2582 : rowsJ2 96 97 41 42 ≤ 13929664003097 := by decide +kernel

theorem rows22240R_2583 : rowsJ2 96 97 42 43 ≤ 15409646938038 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2571
#print axioms SieveCert.rows22240R_2583
