/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 636–648 of 4715

File 62 of 351: the parts `rows22250R_636` … `rows22250R_648` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 97866 in units of a depth-4 test: row 53 columns 39–39, row 53 columns
40–40, row 53 columns 41–41, row 53 columns 42–42, row 53 columns 43–43, row 53 columns 44–44, row 53 columns 45–45,
row 53 columns 46–46, row 53 columns 47–47, row 53 columns 48–48, row 53 columns 49–49, row 53 columns 50–50, row 53
columns 51–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_636 : rowsJ2 53 54 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_637 : rowsJ2 53 54 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_638 : rowsJ2 53 54 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_639 : rowsJ2 53 54 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_640 : rowsJ2 53 54 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_641 : rowsJ2 53 54 44 45 ≤ 73761264614 := by decide +kernel

theorem rows22250R_642 : rowsJ2 53 54 45 46 ≤ 289513136736 := by decide +kernel

theorem rows22250R_643 : rowsJ2 53 54 46 47 ≤ 863718633405 := by decide +kernel

theorem rows22250R_644 : rowsJ2 53 54 47 48 ≤ 1715211229152 := by decide +kernel

theorem rows22250R_645 : rowsJ2 53 54 48 49 ≤ 2534481387845 := by decide +kernel

theorem rows22250R_646 : rowsJ2 53 54 49 50 ≤ 3466655113880 := by decide +kernel

theorem rows22250R_647 : rowsJ2 53 54 50 51 ≤ 4656995955664 := by decide +kernel

theorem rows22250R_648 : rowsJ2 53 54 51 52 ≤ 6101712495355 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_636
#print axioms SieveCert.rows22250R_648
