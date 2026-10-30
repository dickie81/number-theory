/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 100–109 of 1136

File 11 of 114: the parts `rows22000E_100` … `rows22000E_109` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 262 s of the kernel: row 64 columns 0–36, row 64 columns 37–47,
row 64 columns 48–54, row 64 columns 55–59, row 64 columns 60–63, row 64 columns 64–271, row 65 columns 0–36, row 65
columns 37–47, row 65 columns 48–54, row 65 columns 55–59), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_100 : rowsJD 64 65 0 37 ≤ 266549401603981 := by decide +kernel

theorem rows22000E_101 : rowsJD 64 65 37 48 ≤ 244207324568872 := by decide +kernel

theorem rows22000E_102 : rowsJD 64 65 48 55 ≤ 120829259307290 := by decide +kernel

theorem rows22000E_103 : rowsJD 64 65 55 60 ≤ 74168484072012 := by decide +kernel

theorem rows22000E_104 : rowsJD 64 65 60 64 ≤ 65568274076185 := by decide +kernel

theorem rows22000E_105 : rowsJD 64 65 64 272 ≤ 19711582161587 := by decide +kernel

theorem rows22000E_106 : rowsJD 65 66 0 37 ≤ 263350060831647 := by decide +kernel

theorem rows22000E_107 : rowsJD 65 66 37 48 ≤ 236529427531272 := by decide +kernel

theorem rows22000E_108 : rowsJD 65 66 48 55 ≤ 115351813277015 := by decide +kernel

theorem rows22000E_109 : rowsJD 65 66 55 60 ≤ 71679678042555 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_100
#print axioms SieveDeep.rows22000E_109
