/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 650–659 of 1136

File 66 of 114: the parts `rows22000E_650` … `rows22000E_659` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 274 s of the kernel: row 131 columns 112–271, row 132 columns
0–47, row 132 columns 48–61, row 132 columns 62–72, row 132 columns 73–79, row 132 columns 80–104, row 132 columns
105–112, row 132 columns 113–271, row 133 columns 0–47, row 133 columns 48–61), each a sum of the costs (`rowsJD`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_650 : rowsJD 131 132 112 272 ≤ 1950523821214834 := by decide +kernel

theorem rows22000E_651 : rowsJD 132 133 0 48 ≤ 106850500056006 := by decide +kernel

theorem rows22000E_652 : rowsJD 132 133 48 62 ≤ 69363512654844 := by decide +kernel

theorem rows22000E_653 : rowsJD 132 133 62 73 ≤ 97889897842259 := by decide +kernel

theorem rows22000E_654 : rowsJD 132 133 73 80 ≤ 297939903535905 := by decide +kernel

theorem rows22000E_655 : rowsJD 132 133 80 105 ≤ 308815048506697 := by decide +kernel

theorem rows22000E_656 : rowsJD 132 133 105 113 ≤ 353985747609173 := by decide +kernel

theorem rows22000E_657 : rowsJD 132 133 113 272 ≤ 2001545524490674 := by decide +kernel

theorem rows22000E_658 : rowsJD 133 134 0 48 ≤ 102925025818267 := by decide +kernel

theorem rows22000E_659 : rowsJD 133 134 48 62 ≤ 64174966949845 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_650
#print axioms SieveDeep.rows22000E_659
