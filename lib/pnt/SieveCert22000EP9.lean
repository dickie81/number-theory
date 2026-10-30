/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 80–89 of 1136

File 9 of 114: the parts `rows22000E_80` … `rows22000E_89` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 253 s of the kernel: row 60 columns 37–47, row 60 columns 48–54,
row 60 columns 55–58, row 60 columns 59–271, row 61 columns 0–36, row 61 columns 37–47, row 61 columns 48–54, row 61
columns 55–58, row 61 columns 59–271, row 62 columns 0–36), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_80 : rowsJD 60 61 37 48 ≤ 273761643012689 := by decide +kernel

theorem rows22000E_81 : rowsJD 60 61 48 55 ≤ 145843774523318 := by decide +kernel

theorem rows22000E_82 : rowsJD 60 61 55 59 ≤ 70343074182339 := by decide +kernel

theorem rows22000E_83 : rowsJD 60 61 59 272 ≤ 34079960412333 := by decide +kernel

theorem rows22000E_84 : rowsJD 61 62 0 37 ≤ 274585517585377 := by decide +kernel

theorem rows22000E_85 : rowsJD 61 62 37 48 ≤ 266395655904896 := by decide +kernel

theorem rows22000E_86 : rowsJD 61 62 48 55 ≤ 138922755502402 := by decide +kernel

theorem rows22000E_87 : rowsJD 61 62 55 59 ≤ 67049173929862 := by decide +kernel

theorem rows22000E_88 : rowsJD 61 62 59 272 ≤ 49397105520753 := by decide +kernel

theorem rows22000E_89 : rowsJD 62 63 0 37 ≤ 272081622022716 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_80
#print axioms SieveDeep.rows22000E_89
