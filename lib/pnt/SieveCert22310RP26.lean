/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 104–107 of 1732

File 26 of 430: the parts `rows22310R_104` … `rows22310R_107` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27584 tests: row 61 columns 55–58, row 61 columns 59–399, row 62 columns
0–34, row 62 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_104 : rowsJ2 61 62 55 59 ≤ 115196826843282 := by decide +kernel

theorem rows22310R_105 : rowsJ2 61 62 59 400 ≤ 103479340293975 := by decide +kernel

theorem rows22310R_106 : rowsJ2 62 63 0 35 ≤ 1128578792688986 := by decide +kernel

theorem rows22310R_107 : rowsJ2 62 63 35 44 ≤ 379290682635004 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_104
#print axioms SieveCert.rows22310R_107
