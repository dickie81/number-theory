/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1626–1629 of 1732

File 409 of 430: the parts `rows22310R_1626` … `rows22310R_1629` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29602 tests: row 210 columns 0–39, row 210 columns 40–399, row 211 columns
0–39, row 211 columns 40–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1626 : rowsJ2 210 211 0 40 ≤ 41486514823640 := by decide +kernel

theorem rows22310R_1627 : rowsJ2 210 211 40 400 ≤ 2417474013438079 := by decide +kernel

theorem rows22310R_1628 : rowsJ2 211 212 0 40 ≤ 45607163205161 := by decide +kernel

theorem rows22310R_1629 : rowsJ2 211 212 40 400 ≤ 2499075177127110 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1626
#print axioms SieveCert.rows22310R_1629
