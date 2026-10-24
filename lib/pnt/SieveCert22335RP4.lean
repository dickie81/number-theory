/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 14–19 of 549

File 4 of 140: the parts `rows22335R_14` … `rows22335R_19` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (6 parts, 29679 tests: row 36 columns 0–34, row 36 columns 35–299, row 37 columns 0–34,
row 37 columns 35–299, row 38 columns 0–34, row 38 columns 35–299), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_14 : rowsJ2 36 37 0 35 ≤ 2707512218617080 := by decide +kernel

theorem rows22335R_15 : rowsJ2 36 37 35 300 ≤ 157831388033967 := by decide +kernel

theorem rows22335R_16 : rowsJ2 37 38 0 35 ≤ 2625432936072491 := by decide +kernel

theorem rows22335R_17 : rowsJ2 37 38 35 300 ≤ 214666798759060 := by decide +kernel

theorem rows22335R_18 : rowsJ2 38 39 0 35 ≤ 2543694260745719 := by decide +kernel

theorem rows22335R_19 : rowsJ2 38 39 35 300 ≤ 260382486845996 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_14
#print axioms SieveCert.rows22335R_19
