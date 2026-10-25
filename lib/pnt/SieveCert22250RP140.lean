/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1372–1377 of 5796

File 140 of 465: the parts `rows22250R_1372` … `rows22250R_1377` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 88598 tests: row 70 columns 58–58, row 70 columns 59–59, row 70 columns
60–60, row 70 columns 61–61, row 70 columns 62–62, row 70 columns 63–63), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1372 : rowsJ2 70 71 58 59 ≤ 7077142019759 := by decide +kernel

theorem rows22250R_1373 : rowsJ2 70 71 59 60 ≤ 7547237600888 := by decide +kernel

theorem rows22250R_1374 : rowsJ2 70 71 60 61 ≤ 8086806068849 := by decide +kernel

theorem rows22250R_1375 : rowsJ2 70 71 61 62 ≤ 7673416451742 := by decide +kernel

theorem rows22250R_1376 : rowsJ2 70 71 62 63 ≤ 7305264406920 := by decide +kernel

theorem rows22250R_1377 : rowsJ2 70 71 63 64 ≤ 6887537658010 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1372
#print axioms SieveCert.rows22250R_1377
