/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 752–760 of 5796

File 81 of 465: the parts `rows22250R_752` … `rows22250R_760` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 96823 tests: row 56 columns 36–36, row 56 columns 37–37, row 56 columns
38–38, row 56 columns 39–39, row 56 columns 40–40, row 56 columns 41–41, row 56 columns 42–42, row 56 columns 43–43,
row 56 columns 44–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_752 : rowsJ2 56 57 36 37 ≤ 432000624 := by decide +kernel

theorem rows22250R_753 : rowsJ2 56 57 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_754 : rowsJ2 56 57 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_755 : rowsJ2 56 57 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_756 : rowsJ2 56 57 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_757 : rowsJ2 56 57 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_758 : rowsJ2 56 57 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_759 : rowsJ2 56 57 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_760 : rowsJ2 56 57 44 45 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_752
#print axioms SieveCert.rows22250R_760
