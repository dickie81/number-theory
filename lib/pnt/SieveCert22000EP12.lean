/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 110–119 of 1136

File 12 of 114: the parts `rows22000E_110` … `rows22000E_119` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 260 s of the kernel: row 65 columns 60–63, row 65 columns 64–271,
row 66 columns 0–36, row 66 columns 37–47, row 66 columns 48–54, row 66 columns 55–59, row 66 columns 60–63, row 66
columns 64–271, row 67 columns 0–36, row 67 columns 37–47), each a sum of the costs (`rowsJD`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_110 : rowsJD 65 66 60 64 ≤ 64372625283646 := by decide +kernel

theorem rows22000E_111 : rowsJD 65 66 64 272 ≤ 34222858965179 := by decide +kernel

theorem rows22000E_112 : rowsJD 66 67 0 37 ≤ 260128829283243 := by decide +kernel

theorem rows22000E_113 : rowsJD 66 67 37 48 ≤ 228828060506913 := by decide +kernel

theorem rows22000E_114 : rowsJD 66 67 48 55 ≤ 110441206841043 := by decide +kernel

theorem rows22000E_115 : rowsJD 66 67 55 60 ≤ 69531474531378 := by decide +kernel

theorem rows22000E_116 : rowsJD 66 67 60 64 ≤ 63261975264971 := by decide +kernel

theorem rows22000E_117 : rowsJD 66 67 64 272 ≤ 45863490941413 := by decide +kernel

theorem rows22000E_118 : rowsJD 67 68 0 37 ≤ 257141845023470 := by decide +kernel

theorem rows22000E_119 : rowsJD 67 68 37 48 ≤ 221061444686509 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_110
#print axioms SieveDeep.rows22000E_119
