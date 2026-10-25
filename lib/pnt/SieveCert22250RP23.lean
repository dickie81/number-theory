/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 291–300 of 5796

File 23 of 465: the parts `rows22250R_291` … `rows22250R_300` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 97462 tests: row 39 columns 38–38, row 39 columns 39–359, row 40 columns
0–13, row 40 columns 14–16, row 40 columns 17–18, row 40 columns 19–20, row 40 columns 21–22, row 40 columns 23–24,
row 40 columns 25–26, row 40 columns 27–27), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_291 : rowsJ2 39 40 38 39 ≤ 531259238226 := by decide +kernel

theorem rows22250R_292 : rowsJ2 39 40 39 360 ≤ 494045308309 := by decide +kernel

theorem rows22250R_293 : rowsJ2 40 41 0 14 ≤ 547300024012 := by decide +kernel

theorem rows22250R_294 : rowsJ2 40 41 14 17 ≤ 1599128640389 := by decide +kernel

theorem rows22250R_295 : rowsJ2 40 41 17 19 ≤ 1567221096110 := by decide +kernel

theorem rows22250R_296 : rowsJ2 40 41 19 21 ≤ 1715339781730 := by decide +kernel

theorem rows22250R_297 : rowsJ2 40 41 21 23 ≤ 1679036018587 := by decide +kernel

theorem rows22250R_298 : rowsJ2 40 41 23 25 ≤ 1512367645454 := by decide +kernel

theorem rows22250R_299 : rowsJ2 40 41 25 27 ≤ 1288027300550 := by decide +kernel

theorem rows22250R_300 : rowsJ2 40 41 27 28 ≤ 557230941612 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_291
#print axioms SieveCert.rows22250R_300
