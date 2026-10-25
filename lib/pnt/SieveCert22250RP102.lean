/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 966–975 of 5796

File 102 of 465: the parts `rows22250R_966` … `rows22250R_975` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 90187 tests: row 61 columns 60–60, row 61 columns 61–359, row 62 columns
0–16, row 62 columns 17–21, row 62 columns 22–23, row 62 columns 24–24, row 62 columns 25–25, row 62 columns 26–26,
row 62 columns 27–27, row 62 columns 28–28), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_966 : rowsJ2 61 62 60 61 ≤ 11948251464283 := by decide +kernel

theorem rows22250R_967 : rowsJ2 61 62 61 360 ≤ 12982002539392 := by decide +kernel

theorem rows22250R_968 : rowsJ2 62 63 0 17 ≤ 2123266314262 := by decide +kernel

theorem rows22250R_969 : rowsJ2 62 63 17 22 ≤ 499636527215 := by decide +kernel

theorem rows22250R_970 : rowsJ2 62 63 22 24 ≤ 90714275681 := by decide +kernel

theorem rows22250R_971 : rowsJ2 62 63 24 25 ≤ 29089312891 := by decide +kernel

theorem rows22250R_972 : rowsJ2 62 63 25 26 ≤ 19400965188 := by decide +kernel

theorem rows22250R_973 : rowsJ2 62 63 26 27 ≤ 12908244657 := by decide +kernel

theorem rows22250R_974 : rowsJ2 62 63 27 28 ≤ 6464602883 := by decide +kernel

theorem rows22250R_975 : rowsJ2 62 63 28 29 ≤ 3222472514 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_966
#print axioms SieveCert.rows22250R_975
