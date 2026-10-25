/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2667–2682 of 5796

File 244 of 465: the parts `rows22250R_2667` … `rows22250R_2682` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 93648 tests: row 96 columns 56–56, row 96 columns 57–57, row 96 columns
58–58, row 96 columns 59–59, row 96 columns 60–61, row 96 columns 62–63, row 96 columns 64–65, row 96 columns 66–68,
row 96 columns 69–72, row 96 columns 73–76, row 96 columns 77–80, row 96 columns 81–82, row 96 columns 83–83, row 96
columns 84–84, row 96 columns 85–85, row 96 columns 86–86), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2667 : rowsJ2 96 97 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2668 : rowsJ2 96 97 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2669 : rowsJ2 96 97 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_2670 : rowsJ2 96 97 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_2671 : rowsJ2 96 97 60 62 ≤ 0 := by decide +kernel

theorem rows22250R_2672 : rowsJ2 96 97 62 64 ≤ 0 := by decide +kernel

theorem rows22250R_2673 : rowsJ2 96 97 64 66 ≤ 0 := by decide +kernel

theorem rows22250R_2674 : rowsJ2 96 97 66 69 ≤ 0 := by decide +kernel

theorem rows22250R_2675 : rowsJ2 96 97 69 73 ≤ 0 := by decide +kernel

theorem rows22250R_2676 : rowsJ2 96 97 73 77 ≤ 0 := by decide +kernel

theorem rows22250R_2677 : rowsJ2 96 97 77 81 ≤ 52770838052 := by decide +kernel

theorem rows22250R_2678 : rowsJ2 96 97 81 83 ≤ 485159388766 := by decide +kernel

theorem rows22250R_2679 : rowsJ2 96 97 83 84 ≤ 548434359515 := by decide +kernel

theorem rows22250R_2680 : rowsJ2 96 97 84 85 ≤ 833597669807 := by decide +kernel

theorem rows22250R_2681 : rowsJ2 96 97 85 86 ≤ 1168138160188 := by decide +kernel

theorem rows22250R_2682 : rowsJ2 96 97 86 87 ≤ 1565836753818 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2667
#print axioms SieveCert.rows22250R_2682
