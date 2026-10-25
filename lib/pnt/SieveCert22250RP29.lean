/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 335–346 of 5796

File 29 of 465: the parts `rows22250R_335` … `rows22250R_346` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 92977 tests: row 41 columns 41–359, row 42 columns 0–13, row 42 columns
14–16, row 42 columns 17–19, row 42 columns 20–21, row 42 columns 22–23, row 42 columns 24–25, row 42 columns 26–26,
row 42 columns 27–27, row 42 columns 28–28, row 42 columns 29–29, row 42 columns 30–30), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_335 : rowsJ2 41 42 41 360 ≤ 263460434340 := by decide +kernel

theorem rows22250R_336 : rowsJ2 42 43 0 14 ≤ 666765934569 := by decide +kernel

theorem rows22250R_337 : rowsJ2 42 43 14 17 ≤ 1692430275093 := by decide +kernel

theorem rows22250R_338 : rowsJ2 42 43 17 20 ≤ 2289819804522 := by decide +kernel

theorem rows22250R_339 : rowsJ2 42 43 20 22 ≤ 1539046007020 := by decide +kernel

theorem rows22250R_340 : rowsJ2 42 43 22 24 ≤ 1384444559081 := by decide +kernel

theorem rows22250R_341 : rowsJ2 42 43 24 26 ≤ 1177387376423 := by decide +kernel

theorem rows22250R_342 : rowsJ2 42 43 26 27 ≤ 510244467303 := by decide +kernel

theorem rows22250R_343 : rowsJ2 42 43 27 28 ≤ 461493849361 := by decide +kernel

theorem rows22250R_344 : rowsJ2 42 43 28 29 ≤ 421090400179 := by decide +kernel

theorem rows22250R_345 : rowsJ2 42 43 29 30 ≤ 386678149439 := by decide +kernel

theorem rows22250R_346 : rowsJ2 42 43 30 31 ≤ 364583865541 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_335
#print axioms SieveCert.rows22250R_346
