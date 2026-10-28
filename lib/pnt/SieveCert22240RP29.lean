/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 335–341 of 5066

File 29 of 387: the parts `rows22240R_335` … `rows22240R_341` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 97946 in units of a depth-4 test: row 41 columns 38–38, row 41 columns
39–39, row 41 columns 40–40, row 41 columns 41–339, row 42 columns 0–13, row 42 columns 14–16, row 42 columns
17–19), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_335 : rowsJ2 41 42 38 39 ≤ 362970405467 := by decide +kernel

theorem rows22240R_336 : rowsJ2 41 42 39 40 ≤ 318906218022 := by decide +kernel

theorem rows22240R_337 : rowsJ2 41 42 40 41 ≤ 273016153145 := by decide +kernel

theorem rows22240R_338 : rowsJ2 41 42 41 340 ≤ 236307400360 := by decide +kernel

theorem rows22240R_339 : rowsJ2 42 43 0 14 ≤ 869564137207 := by decide +kernel

theorem rows22240R_340 : rowsJ2 42 43 14 17 ≤ 2124976255083 := by decide +kernel

theorem rows22240R_341 : rowsJ2 42 43 17 20 ≤ 2876057871528 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_335
#print axioms SieveCert.rows22240R_341
