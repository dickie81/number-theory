/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1050–1053 of 1732

File 263 of 430: the parts `rows22310R_1050` … `rows22310R_1053` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27159 tests: row 137 columns 40–67, row 137 columns 68–72, row 137 columns
73–75, row 137 columns 76–78), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1050 : rowsJ2 137 138 40 68 ≤ 81428436568618 := by decide +kernel

theorem rows22310R_1051 : rowsJ2 137 138 68 73 ≤ 6447905803581 := by decide +kernel

theorem rows22310R_1052 : rowsJ2 137 138 73 76 ≤ 3247544141459 := by decide +kernel

theorem rows22310R_1053 : rowsJ2 137 138 76 79 ≤ 1620874153838 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1050
#print axioms SieveCert.rows22310R_1053
