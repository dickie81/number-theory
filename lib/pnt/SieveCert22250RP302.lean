/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3484–3498 of 5796

File 302 of 465: the parts `rows22250R_3484` … `rows22250R_3498` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98532 tests: row 113 columns 49–51, row 113 columns 52–56, row 113 columns
57–66, row 113 columns 67–73, row 113 columns 74–77, row 113 columns 78–80, row 113 columns 81–82, row 113 columns
83–83, row 113 columns 84–84, row 113 columns 85–85, row 113 columns 86–87, row 113 columns 88–89, row 113 columns
90–91, row 113 columns 92–93, row 113 columns 94–95), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3484 : rowsJ2 113 114 49 52 ≤ 2492054119540 := by decide +kernel

theorem rows22250R_3485 : rowsJ2 113 114 52 57 ≤ 317126128576 := by decide +kernel

theorem rows22250R_3486 : rowsJ2 113 114 57 67 ≤ 184536538200 := by decide +kernel

theorem rows22250R_3487 : rowsJ2 113 114 67 74 ≤ 0 := by decide +kernel

theorem rows22250R_3488 : rowsJ2 113 114 74 78 ≤ 0 := by decide +kernel

theorem rows22250R_3489 : rowsJ2 113 114 78 81 ≤ 47260327169 := by decide +kernel

theorem rows22250R_3490 : rowsJ2 113 114 81 83 ≤ 433509979167 := by decide +kernel

theorem rows22250R_3491 : rowsJ2 113 114 83 84 ≤ 486462277456 := by decide +kernel

theorem rows22250R_3492 : rowsJ2 113 114 84 85 ≤ 568662419657 := by decide +kernel

theorem rows22250R_3493 : rowsJ2 113 114 85 86 ≤ 492505948011 := by decide +kernel

theorem rows22250R_3494 : rowsJ2 113 114 86 88 ≤ 820475553245 := by decide +kernel

theorem rows22250R_3495 : rowsJ2 113 114 88 90 ≤ 969035896613 := by decide +kernel

theorem rows22250R_3496 : rowsJ2 113 114 90 92 ≤ 1596447768561 := by decide +kernel

theorem rows22250R_3497 : rowsJ2 113 114 92 94 ≤ 2721325439010 := by decide +kernel

theorem rows22250R_3498 : rowsJ2 113 114 94 96 ≤ 4364219741905 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3484
#print axioms SieveCert.rows22250R_3498
