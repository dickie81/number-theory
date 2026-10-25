/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1049–1057 of 5796

File 110 of 465: the parts `rows22250R_1049` … `rows22250R_1057` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 99814 tests: row 63 columns 60–60, row 63 columns 61–61, row 63 columns
62–62, row 63 columns 63–359, row 64 columns 0–16, row 64 columns 17–21, row 64 columns 22–23, row 64 columns 24–24,
row 64 columns 25–25), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22250R_1049 : rowsJ2 63 64 60 61 ≤ 11220546861032 := by decide +kernel

theorem rows22250R_1050 : rowsJ2 63 64 61 62 ≤ 12108396153790 := by decide +kernel

theorem rows22250R_1051 : rowsJ2 63 64 62 63 ≤ 12806645991897 := by decide +kernel

theorem rows22250R_1052 : rowsJ2 63 64 63 360 ≤ 13470679455005 := by decide +kernel

theorem rows22250R_1053 : rowsJ2 64 65 0 17 ≤ 1876807659097 := by decide +kernel

theorem rows22250R_1054 : rowsJ2 64 65 17 22 ≤ 338615145961 := by decide +kernel

theorem rows22250R_1055 : rowsJ2 64 65 22 24 ≤ 48957762726 := by decide +kernel

theorem rows22250R_1056 : rowsJ2 64 65 24 25 ≤ 13025058511 := by decide +kernel

theorem rows22250R_1057 : rowsJ2 64 65 25 26 ≤ 6520803593 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1049
#print axioms SieveCert.rows22250R_1057
