/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 627–635 of 4715

File 61 of 351: the parts `rows22250R_627` … `rows22250R_635` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, work 92510 in units of a depth-4 test: row 53 columns 30–30, row 53 columns
31–31, row 53 columns 32–32, row 53 columns 33–33, row 53 columns 34–34, row 53 columns 35–35, row 53 columns 36–36,
row 53 columns 37–37, row 53 columns 38–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_627 : rowsJ2 53 54 30 31 ≤ 20270025085 := by decide +kernel

theorem rows22250R_628 : rowsJ2 53 54 31 32 ≤ 10151640761 := by decide +kernel

theorem rows22250R_629 : rowsJ2 53 54 32 33 ≤ 4456046305 := by decide +kernel

theorem rows22250R_630 : rowsJ2 53 54 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_631 : rowsJ2 53 54 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_632 : rowsJ2 53 54 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_633 : rowsJ2 53 54 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_634 : rowsJ2 53 54 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_635 : rowsJ2 53 54 38 39 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_627
#print axioms SieveCert.rows22250R_635
