/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 793–802 of 5066

File 80 of 387: the parts `rows22240R_793` … `rows22240R_802` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 97881 in units of a depth-4 test: row 57 columns 31–31, row 57 columns
32–32, row 57 columns 33–33, row 57 columns 34–34, row 57 columns 35–35, row 57 columns 36–36, row 57 columns 37–37,
row 57 columns 38–38, row 57 columns 39–39, row 57 columns 40–40), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_793 : rowsJ2 57 58 31 32 ≤ 16665441453 := by decide +kernel

theorem rows22240R_794 : rowsJ2 57 58 32 33 ≤ 8088572805 := by decide +kernel

theorem rows22240R_795 : rowsJ2 57 58 33 34 ≤ 4035866601 := by decide +kernel

theorem rows22240R_796 : rowsJ2 57 58 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_797 : rowsJ2 57 58 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_798 : rowsJ2 57 58 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_799 : rowsJ2 57 58 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_800 : rowsJ2 57 58 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_801 : rowsJ2 57 58 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_802 : rowsJ2 57 58 40 41 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_793
#print axioms SieveCert.rows22240R_802
