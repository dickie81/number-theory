/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 767–778 of 4715

File 73 of 351: the parts `rows22250R_767` … `rows22250R_778` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 96692 in units of a depth-4 test: row 57 columns 29–29, row 57 columns
30–30, row 57 columns 31–31, row 57 columns 32–32, row 57 columns 33–33, row 57 columns 34–34, row 57 columns 35–35,
row 57 columns 36–36, row 57 columns 37–37, row 57 columns 38–38, row 57 columns 39–39, row 57 columns 40–40), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_767 : rowsJ2 57 58 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_768 : rowsJ2 57 58 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_769 : rowsJ2 57 58 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_770 : rowsJ2 57 58 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_771 : rowsJ2 57 58 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_772 : rowsJ2 57 58 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_773 : rowsJ2 57 58 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_774 : rowsJ2 57 58 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_775 : rowsJ2 57 58 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_776 : rowsJ2 57 58 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_777 : rowsJ2 57 58 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_778 : rowsJ2 57 58 40 41 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_767
#print axioms SieveCert.rows22250R_778
