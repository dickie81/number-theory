/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2489–2498 of 5796

File 229 of 465: the parts `rows22250R_2489` … `rows22250R_2498` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 87068 tests: row 92 columns 81–82, row 92 columns 83–83, row 92 columns
84–84, row 92 columns 85–85, row 92 columns 86–86, row 92 columns 87–87, row 92 columns 88–88, row 92 columns 89–89,
row 92 columns 90–90, row 92 columns 91–91), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2489 : rowsJ2 92 93 81 83 ≤ 498845247400 := by decide +kernel

theorem rows22250R_2490 : rowsJ2 92 93 83 84 ≤ 563905141466 := by decide +kernel

theorem rows22250R_2491 : rowsJ2 92 93 84 85 ≤ 857112622066 := by decide +kernel

theorem rows22250R_2492 : rowsJ2 92 93 85 86 ≤ 1202212025031 := by decide +kernel

theorem rows22250R_2493 : rowsJ2 92 93 86 87 ≤ 1611956749071 := by decide +kernel

theorem rows22250R_2494 : rowsJ2 92 93 87 88 ≤ 2126233286397 := by decide +kernel

theorem rows22250R_2495 : rowsJ2 92 93 88 89 ≤ 2765048529494 := by decide +kernel

theorem rows22250R_2496 : rowsJ2 92 93 89 90 ≤ 3519920506825 := by decide +kernel

theorem rows22250R_2497 : rowsJ2 92 93 90 91 ≤ 4415021624812 := by decide +kernel

theorem rows22250R_2498 : rowsJ2 92 93 91 92 ≤ 5443857747478 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2489
#print axioms SieveCert.rows22250R_2498
