/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2683–2689 of 5796

File 245 of 465: the parts `rows22250R_2683` … `rows22250R_2689` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 95572 tests: row 96 columns 87–87, row 96 columns 88–88, row 96 columns
89–89, row 96 columns 90–90, row 96 columns 91–91, row 96 columns 92–92, row 96 columns 93–93), each a sum of
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

theorem rows22250R_2683 : rowsJ2 96 97 87 88 ≤ 2072181580049 := by decide +kernel

theorem rows22250R_2684 : rowsJ2 96 97 88 89 ≤ 2709090708776 := by decide +kernel

theorem rows22250R_2685 : rowsJ2 96 97 89 90 ≤ 3471032835837 := by decide +kernel

theorem rows22250R_2686 : rowsJ2 96 97 90 91 ≤ 4381332028717 := by decide +kernel

theorem rows22250R_2687 : rowsJ2 96 97 91 92 ≤ 5359117411866 := by decide +kernel

theorem rows22250R_2688 : rowsJ2 96 97 92 93 ≤ 6188478729601 := by decide +kernel

theorem rows22250R_2689 : rowsJ2 96 97 93 94 ≤ 5549914997550 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2683
#print axioms SieveCert.rows22250R_2689
