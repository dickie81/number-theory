/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 774–777 of 1732

File 194 of 430: the parts `rows22310R_774` … `rows22310R_777` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28083 tests: row 120 columns 96–97, row 120 columns 98–100, row 120 columns
101–103, row 120 columns 104–106), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_774 : rowsJ2 120 121 96 98 ≤ 274408543673 := by decide +kernel

theorem rows22310R_775 : rowsJ2 120 121 98 101 ≤ 209058999832 := by decide +kernel

theorem rows22310R_776 : rowsJ2 120 121 101 104 ≤ 970421511738 := by decide +kernel

theorem rows22310R_777 : rowsJ2 120 121 104 107 ≤ 3019003667137 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_774
#print axioms SieveCert.rows22310R_777
