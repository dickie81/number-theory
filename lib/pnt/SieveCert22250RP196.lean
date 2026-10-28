/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2372–2384 of 4715

File 196 of 351: the parts `rows22250R_2372` … `rows22250R_2384` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 93500 in units of a depth-4 test: row 94 columns 55–56, row 94 columns
57–59, row 94 columns 60–64, row 94 columns 65–70, row 94 columns 71–75, row 94 columns 76–78, row 94 columns 79–79,
row 94 columns 80–80, row 94 columns 81–81, row 94 columns 82–82, row 94 columns 83–83, row 94 columns 84–84, row 94
columns 85–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2372 : rowsJ2 94 95 55 57 ≤ 0 := by decide +kernel

theorem rows22250R_2373 : rowsJ2 94 95 57 60 ≤ 0 := by decide +kernel

theorem rows22250R_2374 : rowsJ2 94 95 60 65 ≤ 0 := by decide +kernel

theorem rows22250R_2375 : rowsJ2 94 95 65 71 ≤ 0 := by decide +kernel

theorem rows22250R_2376 : rowsJ2 94 95 71 76 ≤ 16200632010 := by decide +kernel

theorem rows22250R_2377 : rowsJ2 94 95 76 79 ≤ 833959585202 := by decide +kernel

theorem rows22250R_2378 : rowsJ2 94 95 79 80 ≤ 782185709056 := by decide +kernel

theorem rows22250R_2379 : rowsJ2 94 95 80 81 ≤ 1144817541817 := by decide +kernel

theorem rows22250R_2380 : rowsJ2 94 95 81 82 ≤ 1582306316369 := by decide +kernel

theorem rows22250R_2381 : rowsJ2 94 95 82 83 ≤ 2166066196888 := by decide +kernel

theorem rows22250R_2382 : rowsJ2 94 95 83 84 ≤ 2925759667619 := by decide +kernel

theorem rows22250R_2383 : rowsJ2 94 95 84 85 ≤ 3756624270430 := by decide +kernel

theorem rows22250R_2384 : rowsJ2 94 95 85 86 ≤ 4384835875994 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2372
#print axioms SieveCert.rows22250R_2384
