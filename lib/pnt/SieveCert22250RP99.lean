/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1082–1089 of 4715

File 99 of 351: the parts `rows22250R_1082` … `rows22250R_1089` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, work 98349 in units of a depth-4 test: row 64 columns 57–57, row 64 columns
58–58, row 64 columns 59–59, row 64 columns 60–60, row 64 columns 61–61, row 64 columns 62–62, row 64 columns 63–63,
row 64 columns 64–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1082 : rowsJ2 64 65 57 58 ≤ 10691895786296 := by decide +kernel

theorem rows22250R_1083 : rowsJ2 64 65 58 59 ≤ 10748580220451 := by decide +kernel

theorem rows22250R_1084 : rowsJ2 64 65 59 60 ≤ 10288068277902 := by decide +kernel

theorem rows22250R_1085 : rowsJ2 64 65 60 61 ≤ 9765491327447 := by decide +kernel

theorem rows22250R_1086 : rowsJ2 64 65 61 62 ≤ 9300200302074 := by decide +kernel

theorem rows22250R_1087 : rowsJ2 64 65 62 63 ≤ 8771340502902 := by decide +kernel

theorem rows22250R_1088 : rowsJ2 64 65 63 64 ≤ 8300098562907 := by decide +kernel

theorem rows22250R_1089 : rowsJ2 64 65 64 340 ≤ 7763712679541 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1082
#print axioms SieveCert.rows22250R_1089
