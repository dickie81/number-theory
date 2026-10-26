/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 79–82 of 561

File 20 of 143: the parts `rows22322R_79` … `rows22322R_82` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24726 tests: row 58 columns 0–34, row 58 columns 35–43, row 58 columns 44–54,
row 58 columns 55–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_79 : rowsJ2 58 59 0 35 ≤ 1117456384488475 := by decide +kernel

theorem rows22322R_80 : rowsJ2 58 59 35 44 ≤ 452009140562416 := by decide +kernel

theorem rows22322R_81 : rowsJ2 58 59 44 55 ≤ 699070258806942 := by decide +kernel

theorem rows22322R_82 : rowsJ2 58 59 55 300 ≤ 190961657206620 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_79
#print axioms SieveCert.rows22322R_82
