/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 510–519 of 1136

File 52 of 114: the parts `rows22000E_510` … `rows22000E_519` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 266 s of the kernel: row 113 columns 60–69, row 113 columns 70–79,
row 113 columns 80–86, row 113 columns 87–92, row 113 columns 93–98, row 113 columns 99–271, row 114 columns 0–39,
row 114 columns 40–59, row 114 columns 60–69, row 114 columns 70–79), each a sum of the costs (`rowsJD`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_510 : rowsJD 113 114 60 70 ≤ 134511491768203 := by decide +kernel

theorem rows22000E_511 : rowsJD 113 114 70 80 ≤ 67260730361361 := by decide +kernel

theorem rows22000E_512 : rowsJD 113 114 80 87 ≤ 83670462348584 := by decide +kernel

theorem rows22000E_513 : rowsJD 113 114 87 93 ≤ 85855000585290 := by decide +kernel

theorem rows22000E_514 : rowsJD 113 114 93 99 ≤ 137256003940209 := by decide +kernel

theorem rows22000E_515 : rowsJD 113 114 99 272 ≤ 61140886739718 := by decide +kernel

theorem rows22000E_516 : rowsJD 114 115 0 40 ≤ 149013131062560 := by decide +kernel

theorem rows22000E_517 : rowsJD 114 115 40 60 ≤ 149170161374780 := by decide +kernel

theorem rows22000E_518 : rowsJD 114 115 60 70 ≤ 140161895162212 := by decide +kernel

theorem rows22000E_519 : rowsJD 114 115 70 80 ≤ 75205846903201 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_510
#print axioms SieveDeep.rows22000E_519
