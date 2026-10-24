/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 144–147 of 549

File 38 of 140: the parts `rows22335R_144` … `rows22335R_147` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28710 tests: row 75 columns 0–34, row 75 columns 35–59, row 75 columns 60–67,
row 75 columns 68–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_144 : rowsJ2 75 76 0 35 ≤ 529078156706695 := by decide +kernel

theorem rows22335R_145 : rowsJ2 75 76 35 60 ≤ 842336990014681 := by decide +kernel

theorem rows22335R_146 : rowsJ2 75 76 60 68 ≤ 42684828366628 := by decide +kernel

theorem rows22335R_147 : rowsJ2 75 76 68 72 ≤ 13347334475616 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_144
#print axioms SieveCert.rows22335R_147
