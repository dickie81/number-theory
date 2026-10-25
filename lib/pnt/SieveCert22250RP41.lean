/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 423–427 of 5796

File 41 of 465: the parts `rows22250R_423` … `rows22250R_427` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (5 parts, 95979 tests: row 45 columns 37–37, row 45 columns 38–38, row 45 columns
39–39, row 45 columns 40–40, row 45 columns 41–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_423 : rowsJ2 45 46 37 38 ≤ 177939235245 := by decide +kernel

theorem rows22250R_424 : rowsJ2 45 46 38 39 ≤ 149097275635 := by decide +kernel

theorem rows22250R_425 : rowsJ2 45 46 39 40 ≤ 124809467379 := by decide +kernel

theorem rows22250R_426 : rowsJ2 45 46 40 41 ≤ 100718754135 := by decide +kernel

theorem rows22250R_427 : rowsJ2 45 46 41 42 ≤ 83414252241 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_423
#print axioms SieveCert.rows22250R_427
