/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1716–1727 of 5796

File 170 of 465: the parts `rows22250R_1716` … `rows22250R_1727` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 94354 tests: row 77 columns 43–43, row 77 columns 44–44, row 77 columns
45–45, row 77 columns 46–46, row 77 columns 47–47, row 77 columns 48–48, row 77 columns 49–49, row 77 columns 50–50,
row 77 columns 51–51, row 77 columns 52–52, row 77 columns 53–53, row 77 columns 54–54), each a sum of refined costs
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

theorem rows22250R_1716 : rowsJ2 77 78 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1717 : rowsJ2 77 78 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1718 : rowsJ2 77 78 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1719 : rowsJ2 77 78 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1720 : rowsJ2 77 78 47 48 ≤ 97395782473 := by decide +kernel

theorem rows22250R_1721 : rowsJ2 77 78 48 49 ≤ 436512211382 := by decide +kernel

theorem rows22250R_1722 : rowsJ2 77 78 49 50 ≤ 812842762094 := by decide +kernel

theorem rows22250R_1723 : rowsJ2 77 78 50 51 ≤ 1222539542654 := by decide +kernel

theorem rows22250R_1724 : rowsJ2 77 78 51 52 ≤ 1759841646584 := by decide +kernel

theorem rows22250R_1725 : rowsJ2 77 78 52 53 ≤ 2361058930421 := by decide +kernel

theorem rows22250R_1726 : rowsJ2 77 78 53 54 ≤ 2823283020880 := by decide +kernel

theorem rows22250R_1727 : rowsJ2 77 78 54 55 ≤ 3105387645172 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1716
#print axioms SieveCert.rows22250R_1727
