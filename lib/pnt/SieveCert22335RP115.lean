/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 443–445 of 549

File 115 of 140: the parts `rows22335R_443` … `rows22335R_445` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 23488 tests: row 126 columns 54–299, row 127 columns 0–45, row 127 columns
46–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_443 : rowsJ2 126 127 54 300 ≤ 1617262245855786 := by decide +kernel

theorem rows22335R_444 : rowsJ2 127 128 0 46 ≤ 148835561757367 := by decide +kernel

theorem rows22335R_445 : rowsJ2 127 128 46 54 ≤ 94771319837455 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_443
#print axioms SieveCert.rows22335R_445
