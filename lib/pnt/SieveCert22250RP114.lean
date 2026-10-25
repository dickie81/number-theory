/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1092–1098 of 5796

File 114 of 465: the parts `rows22250R_1092` … `rows22250R_1098` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 97730 tests: row 64 columns 60–60, row 64 columns 61–61, row 64 columns
62–62, row 64 columns 63–63, row 64 columns 64–359, row 65 columns 0–17, row 65 columns 18–21), each a sum of
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

theorem rows22250R_1092 : rowsJ2 64 65 60 61 ≤ 10839154765126 := by decide +kernel

theorem rows22250R_1093 : rowsJ2 64 65 61 62 ≤ 11634147114706 := by decide +kernel

theorem rows22250R_1094 : rowsJ2 64 65 62 63 ≤ 12278247028830 := by decide +kernel

theorem rows22250R_1095 : rowsJ2 64 65 63 64 ≤ 12846949069156 := by decide +kernel

theorem rows22250R_1096 : rowsJ2 64 65 64 360 ≤ 12331520013257 := by decide +kernel

theorem rows22250R_1097 : rowsJ2 65 66 0 18 ≤ 1833123977707 := by decide +kernel

theorem rows22250R_1098 : rowsJ2 65 66 18 22 ≤ 187772153821 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1092
#print axioms SieveCert.rows22250R_1098
