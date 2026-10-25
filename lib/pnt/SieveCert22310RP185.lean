/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 737–740 of 1732

File 185 of 430: the parts `rows22310R_737` … `rows22310R_740` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27577 tests: row 118 columns 99–100, row 118 columns 101–103, row 118 columns
104–106, row 118 columns 107–109), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_737 : rowsJ2 118 119 99 101 ≤ 350726385404 := by decide +kernel

theorem rows22310R_738 : rowsJ2 118 119 101 104 ≤ 1054738418329 := by decide +kernel

theorem rows22310R_739 : rowsJ2 118 119 104 107 ≤ 2706044679880 := by decide +kernel

theorem rows22310R_740 : rowsJ2 118 119 107 110 ≤ 5454651017031 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_737
#print axioms SieveCert.rows22310R_740
