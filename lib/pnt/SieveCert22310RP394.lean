/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1565–1568 of 1732

File 394 of 430: the parts `rows22310R_1565` … `rows22310R_1568` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23742 tests: row 192 columns 52–56, row 192 columns 57–125, row 192 columns
126–399, row 193 columns 0–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1565 : rowsJ2 192 193 52 57 ≤ 58247599816672 := by decide +kernel

theorem rows22310R_1566 : rowsJ2 192 193 57 126 ≤ 145982422989976 := by decide +kernel

theorem rows22310R_1567 : rowsJ2 192 193 126 400 ≤ 1980679862223770 := by decide +kernel

theorem rows22310R_1568 : rowsJ2 193 194 0 46 ≤ 34807956125686 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1565
#print axioms SieveCert.rows22310R_1568
