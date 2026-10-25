/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 309–312 of 5796

File 25 of 465: the parts `rows22250R_309` … `rows22250R_312` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (4 parts, 88544 tests: row 40 columns 36–36, row 40 columns 37–37, row 40 columns
38–38, row 40 columns 39–39), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_309 : rowsJ2 40 41 36 37 ≤ 511425835902 := by decide +kernel

theorem rows22250R_310 : rowsJ2 40 41 37 38 ≤ 481521719690 := by decide +kernel

theorem rows22250R_311 : rowsJ2 40 41 38 39 ≤ 455660081036 := by decide +kernel

theorem rows22250R_312 : rowsJ2 40 41 39 40 ≤ 411561840550 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_309
#print axioms SieveCert.rows22250R_312
