/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1007–1016 of 5796

File 106 of 465: the parts `rows22250R_1007` … `rows22250R_1016` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 98224 tests: row 62 columns 60–60, row 62 columns 61–61, row 62 columns
62–359, row 63 columns 0–16, row 63 columns 17–21, row 63 columns 22–23, row 63 columns 24–24, row 63 columns 25–25,
row 63 columns 26–26, row 63 columns 27–27), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1007 : rowsJ2 62 63 60 61 ≤ 11603074101071 := by decide +kernel

theorem rows22250R_1008 : rowsJ2 62 63 61 62 ≤ 12544548224686 := by decide +kernel

theorem rows22250R_1009 : rowsJ2 62 63 62 360 ≤ 13335913584635 := by decide +kernel

theorem rows22250R_1010 : rowsJ2 63 64 0 17 ≤ 2000451652564 := by decide +kernel

theorem rows22250R_1011 : rowsJ2 63 64 17 22 ≤ 416026396994 := by decide +kernel

theorem rows22250R_1012 : rowsJ2 63 64 22 24 ≤ 68285613186 := by decide +kernel

theorem rows22250R_1013 : rowsJ2 63 64 24 25 ≤ 19489528472 := by decide +kernel

theorem rows22250R_1014 : rowsJ2 63 64 25 26 ≤ 12964851684 := by decide +kernel

theorem rows22250R_1015 : rowsJ2 63 64 26 27 ≤ 6491822253 := by decide +kernel

theorem rows22250R_1016 : rowsJ2 63 64 27 28 ≤ 3235492150 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1007
#print axioms SieveCert.rows22250R_1016
