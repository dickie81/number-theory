/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 823–831 of 5796

File 88 of 465: the parts `rows22250R_823` … `rows22250R_831` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 94604 tests: row 58 columns 34–34, row 58 columns 35–35, row 58 columns
36–36, row 58 columns 37–37, row 58 columns 38–38, row 58 columns 39–39, row 58 columns 40–40, row 58 columns 41–41,
row 58 columns 42–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22250R_823 : rowsJ2 58 59 34 35 ≤ 434104819 := by decide +kernel

theorem rows22250R_824 : rowsJ2 58 59 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_825 : rowsJ2 58 59 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_826 : rowsJ2 58 59 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_827 : rowsJ2 58 59 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_828 : rowsJ2 58 59 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_829 : rowsJ2 58 59 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_830 : rowsJ2 58 59 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_831 : rowsJ2 58 59 42 43 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_823
#print axioms SieveCert.rows22250R_831
