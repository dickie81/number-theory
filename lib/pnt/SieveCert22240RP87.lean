/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 870–880 of 5066

File 87 of 387: the parts `rows22240R_870` … `rows22240R_880` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 94214 in units of a depth-4 test: row 59 columns 31–31, row 59 columns
32–32, row 59 columns 33–33, row 59 columns 34–34, row 59 columns 35–35, row 59 columns 36–36, row 59 columns 37–37,
row 59 columns 38–38, row 59 columns 39–39, row 59 columns 40–40, row 59 columns 41–41), each a sum of refined costs
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

theorem rows22240R_870 : rowsJ2 59 60 31 32 ≤ 4061456391 := by decide +kernel

theorem rows22240R_871 : rowsJ2 59 60 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_872 : rowsJ2 59 60 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_873 : rowsJ2 59 60 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_874 : rowsJ2 59 60 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_875 : rowsJ2 59 60 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_876 : rowsJ2 59 60 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_877 : rowsJ2 59 60 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_878 : rowsJ2 59 60 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_879 : rowsJ2 59 60 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_880 : rowsJ2 59 60 41 42 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_870
#print axioms SieveCert.rows22240R_880
