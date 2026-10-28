/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 803–814 of 5066

File 81 of 387: the parts `rows22240R_803` … `rows22240R_814` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 93332 in units of a depth-4 test: row 57 columns 41–41, row 57 columns
42–42, row 57 columns 43–43, row 57 columns 44–44, row 57 columns 45–45, row 57 columns 46–46, row 57 columns 47–47,
row 57 columns 48–48, row 57 columns 49–49, row 57 columns 50–50, row 57 columns 51–51, row 57 columns 52–52), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_803 : rowsJ2 57 58 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_804 : rowsJ2 57 58 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_805 : rowsJ2 57 58 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_806 : rowsJ2 57 58 44 45 ≤ 71988271570 := by decide +kernel

theorem rows22240R_807 : rowsJ2 57 58 45 46 ≤ 210525533130 := by decide +kernel

theorem rows22240R_808 : rowsJ2 57 58 46 47 ≤ 410554291732 := by decide +kernel

theorem rows22240R_809 : rowsJ2 57 58 47 48 ≤ 876567561679 := by decide +kernel

theorem rows22240R_810 : rowsJ2 57 58 48 49 ≤ 1674682111381 := by decide +kernel

theorem rows22240R_811 : rowsJ2 57 58 49 50 ≤ 2582579603044 := by decide +kernel

theorem rows22240R_812 : rowsJ2 57 58 50 51 ≤ 3523910391428 := by decide +kernel

theorem rows22240R_813 : rowsJ2 57 58 51 52 ≤ 4636583378796 := by decide +kernel

theorem rows22240R_814 : rowsJ2 57 58 52 53 ≤ 6060218797299 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_803
#print axioms SieveCert.rows22240R_814
