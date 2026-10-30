/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 440–449 of 1136

File 45 of 114: the parts `rows22000E_440` … `rows22000E_449` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 269 s of the kernel: row 105 columns 105–271, row 106 columns
0–38, row 106 columns 39–53, row 106 columns 54–67, row 106 columns 68–75, row 106 columns 76–83, row 106 columns
84–89, row 106 columns 90–94, row 106 columns 95–98, row 106 columns 99–102), each a sum of the costs (`rowsJD`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22000E.lean`.
-/
import SieveGrid22000E

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveDeep

open SieveCert

section

attribute [local instance] grid22000E ibPar22000E

theorem rows22000E_440 : rowsJD 105 106 105 272 ≤ 69923202094327 := by decide +kernel

theorem rows22000E_441 : rowsJD 106 107 0 39 ≤ 136325315854522 := by decide +kernel

theorem rows22000E_442 : rowsJD 106 107 39 54 ≤ 163111580942878 := by decide +kernel

theorem rows22000E_443 : rowsJD 106 107 54 68 ≤ 109939061613113 := by decide +kernel

theorem rows22000E_444 : rowsJD 106 107 68 76 ≤ 47153317345158 := by decide +kernel

theorem rows22000E_445 : rowsJD 106 107 76 84 ≤ 28685442718958 := by decide +kernel

theorem rows22000E_446 : rowsJD 106 107 84 90 ≤ 47414897856515 := by decide +kernel

theorem rows22000E_447 : rowsJD 106 107 90 95 ≤ 93364095674297 := by decide +kernel

theorem rows22000E_448 : rowsJD 106 107 95 99 ≤ 133732705154516 := by decide +kernel

theorem rows22000E_449 : rowsJD 106 107 99 103 ≤ 189038934145133 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_440
#print axioms SieveDeep.rows22000E_449
