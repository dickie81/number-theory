/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 180–183 of 549

File 47 of 140: the parts `rows22335R_180` … `rows22335R_183` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29936 tests: row 81 columns 0–35, row 81 columns 36–61, row 81 columns 62–67,
row 81 columns 68–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22335R_180 : rowsJ2 81 82 0 36 ≤ 559026796643607 := by decide +kernel

theorem rows22335R_181 : rowsJ2 81 82 36 62 ≤ 523614331796696 := by decide +kernel

theorem rows22335R_182 : rowsJ2 81 82 62 68 ≤ 3308221716414 := by decide +kernel

theorem rows22335R_183 : rowsJ2 81 82 68 72 ≤ 11220455853156 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_180
#print axioms SieveCert.rows22335R_183
