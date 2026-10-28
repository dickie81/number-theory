/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 671–683 of 4715

File 65 of 351: the parts `rows22250R_671` … `rows22250R_683` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 96417 in units of a depth-4 test: row 54 columns 40–40, row 54 columns
41–41, row 54 columns 42–42, row 54 columns 43–43, row 54 columns 44–44, row 54 columns 45–45, row 54 columns 46–46,
row 54 columns 47–47, row 54 columns 48–48, row 54 columns 49–49, row 54 columns 50–50, row 54 columns 51–51, row 54
columns 52–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_671 : rowsJ2 54 55 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_672 : rowsJ2 54 55 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_673 : rowsJ2 54 55 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_674 : rowsJ2 54 55 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_675 : rowsJ2 54 55 44 45 ≤ 73031187433 := by decide +kernel

theorem rows22250R_676 : rowsJ2 54 55 45 46 ≤ 286647582088 := by decide +kernel

theorem rows22250R_677 : rowsJ2 54 55 46 47 ≤ 855169684739 := by decide +kernel

theorem rows22250R_678 : rowsJ2 54 55 47 48 ≤ 1698234343179 := by decide +kernel

theorem rows22250R_679 : rowsJ2 54 55 48 49 ≤ 2509395497092 := by decide +kernel

theorem rows22250R_680 : rowsJ2 54 55 49 50 ≤ 3432342716922 := by decide +kernel

theorem rows22250R_681 : rowsJ2 54 55 50 51 ≤ 4610901755749 := by decide +kernel

theorem rows22250R_682 : rowsJ2 54 55 51 52 ≤ 6041318722571 := by decide +kernel

theorem rows22250R_683 : rowsJ2 54 55 52 53 ≤ 7414487932596 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_671
#print axioms SieveCert.rows22250R_683
