/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 696–706 of 4715

File 67 of 351: the parts `rows22250R_696` … `rows22250R_706` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, work 97763 in units of a depth-4 test: row 55 columns 30–30, row 55 columns
31–31, row 55 columns 32–32, row 55 columns 33–33, row 55 columns 34–34, row 55 columns 35–35, row 55 columns 36–36,
row 55 columns 37–37, row 55 columns 38–38, row 55 columns 39–39, row 55 columns 40–40), each a sum of refined costs
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

theorem rows22250R_696 : rowsJ2 55 56 30 31 ≤ 4482125760 := by decide +kernel

theorem rows22250R_697 : rowsJ2 55 56 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_698 : rowsJ2 55 56 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_699 : rowsJ2 55 56 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_700 : rowsJ2 55 56 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_701 : rowsJ2 55 56 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_702 : rowsJ2 55 56 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_703 : rowsJ2 55 56 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_704 : rowsJ2 55 56 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_705 : rowsJ2 55 56 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_706 : rowsJ2 55 56 40 41 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_696
#print axioms SieveCert.rows22250R_706
