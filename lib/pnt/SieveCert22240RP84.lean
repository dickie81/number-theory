/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 836–848 of 5066

File 84 of 387: the parts `rows22240R_836` … `rows22240R_848` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 96547 in units of a depth-4 test: row 58 columns 36–36, row 58 columns
37–37, row 58 columns 38–38, row 58 columns 39–39, row 58 columns 40–40, row 58 columns 41–41, row 58 columns 42–42,
row 58 columns 43–43, row 58 columns 44–44, row 58 columns 45–45, row 58 columns 46–46, row 58 columns 47–47, row 58
columns 48–48), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_836 : rowsJ2 58 59 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_837 : rowsJ2 58 59 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_838 : rowsJ2 58 59 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_839 : rowsJ2 58 59 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_840 : rowsJ2 58 59 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_841 : rowsJ2 58 59 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_842 : rowsJ2 58 59 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_843 : rowsJ2 58 59 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_844 : rowsJ2 58 59 44 45 ≤ 71300306545 := by decide +kernel

theorem rows22240R_845 : rowsJ2 58 59 45 46 ≤ 208513619240 := by decide +kernel

theorem rows22240R_846 : rowsJ2 58 59 46 47 ≤ 406630777703 := by decide +kernel

theorem rows22240R_847 : rowsJ2 58 59 47 48 ≤ 868190532882 := by decide +kernel

theorem rows22240R_848 : rowsJ2 58 59 48 49 ≤ 1658677799922 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_836
#print axioms SieveCert.rows22240R_848
