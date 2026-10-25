/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 315–324 of 4715

File 28 of 351: the parts `rows22250R_315` … `rows22250R_324` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 94696 tests: row 41 columns 39–39, row 41 columns 40–40, row 41 columns
41–339, row 42 columns 0–13, row 42 columns 14–17, row 42 columns 18–20, row 42 columns 21–23, row 42 columns 24–25,
row 42 columns 26–26, row 42 columns 27–27), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_315 : rowsJ2 41 42 39 40 ≤ 167495595514 := by decide +kernel

theorem rows22250R_316 : rowsJ2 41 42 40 41 ≤ 137823212954 := by decide +kernel

theorem rows22250R_317 : rowsJ2 41 42 41 340 ≤ 110829471322 := by decide +kernel

theorem rows22250R_318 : rowsJ2 42 43 0 14 ≤ 1514446310235 := by decide +kernel

theorem rows22250R_319 : rowsJ2 42 43 14 18 ≤ 3192858283404 := by decide +kernel

theorem rows22250R_320 : rowsJ2 42 43 18 21 ≤ 2433794715834 := by decide +kernel

theorem rows22250R_321 : rowsJ2 42 43 21 24 ≤ 1963973234757 := by decide +kernel

theorem rows22250R_322 : rowsJ2 42 43 24 26 ≤ 1006232447824 := by decide +kernel

theorem rows22250R_323 : rowsJ2 42 43 26 27 ≤ 426009041161 := by decide +kernel

theorem rows22250R_324 : rowsJ2 42 43 27 28 ≤ 384962708348 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_315
#print axioms SieveCert.rows22250R_324
