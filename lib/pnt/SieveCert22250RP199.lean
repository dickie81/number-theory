/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2412–2424 of 4715

File 199 of 351: the parts `rows22250R_2412` … `rows22250R_2424` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 89441 tests: row 95 columns 52–53, row 95 columns 54–55, row 95 columns
56–58, row 95 columns 59–63, row 95 columns 64–70, row 95 columns 71–75, row 95 columns 76–78, row 95 columns 79–79,
row 95 columns 80–80, row 95 columns 81–81, row 95 columns 82–82, row 95 columns 83–83, row 95 columns 84–84), each
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

theorem rows22250R_2412 : rowsJ2 95 96 52 54 ≤ 3477142746698 := by decide +kernel

theorem rows22250R_2413 : rowsJ2 95 96 54 56 ≤ 517366846097 := by decide +kernel

theorem rows22250R_2414 : rowsJ2 95 96 56 59 ≤ 0 := by decide +kernel

theorem rows22250R_2415 : rowsJ2 95 96 59 64 ≤ 0 := by decide +kernel

theorem rows22250R_2416 : rowsJ2 95 96 64 71 ≤ 0 := by decide +kernel

theorem rows22250R_2417 : rowsJ2 95 96 71 76 ≤ 16086568875 := by decide +kernel

theorem rows22250R_2418 : rowsJ2 95 96 76 79 ≤ 828087959616 := by decide +kernel

theorem rows22250R_2419 : rowsJ2 95 96 79 80 ≤ 776678605713 := by decide +kernel

theorem rows22250R_2420 : rowsJ2 95 96 80 81 ≤ 1135462112018 := by decide +kernel

theorem rows22250R_2421 : rowsJ2 95 96 81 82 ≤ 1570072735595 := by decide +kernel

theorem rows22250R_2422 : rowsJ2 95 96 82 83 ≤ 2153565842442 := by decide +kernel

theorem rows22250R_2423 : rowsJ2 95 96 83 84 ≤ 2914760259127 := by decide +kernel

theorem rows22250R_2424 : rowsJ2 95 96 84 85 ≤ 3552052974619 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2412
#print axioms SieveCert.rows22250R_2424
