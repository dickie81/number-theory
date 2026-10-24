/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 208–211 of 549

File 54 of 140: the parts `rows22335R_208` … `rows22335R_211` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28988 tests: row 85 columns 0–38, row 85 columns 39–61, row 85 columns 62–66,
row 85 columns 67–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22335R_208 : rowsJ2 85 86 0 39 ≤ 645177268370286 := by decide +kernel

theorem rows22335R_209 : rowsJ2 85 86 39 62 ≤ 262749900943268 := by decide +kernel

theorem rows22335R_210 : rowsJ2 85 86 62 67 ≤ 1583859261270 := by decide +kernel

theorem rows22335R_211 : rowsJ2 85 86 67 71 ≤ 6405683078658 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_208
#print axioms SieveCert.rows22335R_211
