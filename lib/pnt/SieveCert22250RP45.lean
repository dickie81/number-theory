/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 450–454 of 5796

File 45 of 465: the parts `rows22250R_450` … `rows22250R_454` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (5 parts, 87996 tests: row 46 columns 39–39, row 46 columns 40–40, row 46 columns
41–41, row 46 columns 42–42, row 46 columns 43–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_450 : rowsJ2 46 47 39 40 ≤ 89500895941 := by decide +kernel

theorem rows22250R_451 : rowsJ2 46 47 40 41 ≤ 74428180652 := by decide +kernel

theorem rows22250R_452 : rowsJ2 46 47 41 42 ≤ 57211870346 := by decide +kernel

theorem rows22250R_453 : rowsJ2 46 47 42 43 ≤ 46162370722 := by decide +kernel

theorem rows22250R_454 : rowsJ2 46 47 43 44 ≤ 32922690145 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_450
#print axioms SieveCert.rows22250R_454
