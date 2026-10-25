/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 715–721 of 5796

File 77 of 465: the parts `rows22250R_715` … `rows22250R_721` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 89951 tests: row 55 columns 34–34, row 55 columns 35–35, row 55 columns
36–36, row 55 columns 37–37, row 55 columns 38–38, row 55 columns 39–39, row 55 columns 40–40), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_715 : rowsJ2 55 56 34 35 ≤ 8934864504 := by decide +kernel

theorem rows22250R_716 : rowsJ2 55 56 35 36 ≤ 4889739652 := by decide +kernel

theorem rows22250R_717 : rowsJ2 55 56 36 37 ≤ 866415016 := by decide +kernel

theorem rows22250R_718 : rowsJ2 55 56 37 38 ≤ 431098287 := by decide +kernel

theorem rows22250R_719 : rowsJ2 55 56 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_720 : rowsJ2 55 56 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_721 : rowsJ2 55 56 40 41 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_715
#print axioms SieveCert.rows22250R_721
