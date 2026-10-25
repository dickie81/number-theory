/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 716–719 of 1732

File 180 of 430: the parts `rows22310R_716` … `rows22310R_719` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24633 tests: row 117 columns 96–97, row 117 columns 98–99, row 117 columns
100–101, row 117 columns 102–104), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_716 : rowsJ2 117 118 96 98 ≤ 803370554273 := by decide +kernel

theorem rows22310R_717 : rowsJ2 117 118 98 100 ≤ 604622307753 := by decide +kernel

theorem rows22310R_718 : rowsJ2 117 118 100 102 ≤ 517593821167 := by decide +kernel

theorem rows22310R_719 : rowsJ2 117 118 102 105 ≤ 1528846406327 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_716
#print axioms SieveCert.rows22310R_719
