/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 760–770 of 5066

File 77 of 387: the parts `rows22240R_760` … `rows22240R_770` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 94922 in units of a depth-4 test: row 56 columns 35–35, row 56 columns
36–36, row 56 columns 37–37, row 56 columns 38–38, row 56 columns 39–39, row 56 columns 40–40, row 56 columns 41–41,
row 56 columns 42–42, row 56 columns 43–43, row 56 columns 44–44, row 56 columns 45–45), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_760 : rowsJ2 56 57 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_761 : rowsJ2 56 57 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_762 : rowsJ2 56 57 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_763 : rowsJ2 56 57 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_764 : rowsJ2 56 57 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_765 : rowsJ2 56 57 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_766 : rowsJ2 56 57 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_767 : rowsJ2 56 57 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_768 : rowsJ2 56 57 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_769 : rowsJ2 56 57 44 45 ≤ 72689642384 := by decide +kernel

theorem rows22240R_770 : rowsJ2 56 57 45 46 ≤ 212576651479 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_760
#print axioms SieveCert.rows22240R_770
