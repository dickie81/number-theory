/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 791–801 of 5796

File 85 of 465: the parts `rows22250R_791` … `rows22250R_801` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 94828 tests: row 57 columns 39–39, row 57 columns 40–40, row 57 columns
41–41, row 57 columns 42–42, row 57 columns 43–43, row 57 columns 44–44, row 57 columns 45–45, row 57 columns 46–46,
row 57 columns 47–47, row 57 columns 48–48, row 57 columns 49–49), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_791 : rowsJ2 57 58 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_792 : rowsJ2 57 58 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_793 : rowsJ2 57 58 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_794 : rowsJ2 57 58 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_795 : rowsJ2 57 58 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_796 : rowsJ2 57 58 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_797 : rowsJ2 57 58 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_798 : rowsJ2 57 58 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_799 : rowsJ2 57 58 47 48 ≤ 115634907670 := by decide +kernel

theorem rows22250R_800 : rowsJ2 57 58 48 49 ≤ 518257033087 := by decide +kernel

theorem rows22250R_801 : rowsJ2 57 58 49 50 ≤ 965062298981 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_791
#print axioms SieveCert.rows22250R_801
