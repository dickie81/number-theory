/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1059–1065 of 5066

File 104 of 387: the parts `rows22240R_1059` … `rows22240R_1065` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 95680 in units of a depth-4 test: row 63 columns 54–54, row 63 columns
55–55, row 63 columns 56–56, row 63 columns 57–57, row 63 columns 58–58, row 63 columns 59–59, row 63 columns
60–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1059 : rowsJ2 63 64 54 55 ≤ 8042811405551 := by decide +kernel

theorem rows22240R_1060 : rowsJ2 63 64 55 56 ≤ 9050355800281 := by decide +kernel

theorem rows22240R_1061 : rowsJ2 63 64 56 57 ≤ 10109836681183 := by decide +kernel

theorem rows22240R_1062 : rowsJ2 63 64 57 58 ≤ 10988541610961 := by decide +kernel

theorem rows22240R_1063 : rowsJ2 63 64 58 59 ≤ 11635918677950 := by decide +kernel

theorem rows22240R_1064 : rowsJ2 63 64 59 60 ≤ 12307109859366 := by decide +kernel

theorem rows22240R_1065 : rowsJ2 63 64 60 61 ≤ 12376914687750 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1059
#print axioms SieveCert.rows22240R_1065
