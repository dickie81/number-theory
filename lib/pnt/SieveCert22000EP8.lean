/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 70–79 of 1136

File 8 of 114: the parts `rows22000E_70` … `rows22000E_79` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 254 s of the kernel: row 58 columns 0–36, row 58 columns 37–47,
row 58 columns 48–54, row 58 columns 55–271, row 59 columns 0–36, row 59 columns 37–47, row 59 columns 48–54, row 59
columns 55–58, row 59 columns 59–271, row 60 columns 0–36), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_70 : rowsJD 58 59 0 37 ≤ 283209073133020 := by decide +kernel

theorem rows22000E_71 : rowsJD 58 59 37 48 ≤ 289403106090109 := by decide +kernel

theorem rows22000E_72 : rowsJD 58 59 48 55 ≤ 160473836902614 := by decide +kernel

theorem rows22000E_73 : rowsJD 58 59 55 272 ≤ 78247420649401 := by decide +kernel

theorem rows22000E_74 : rowsJD 59 60 0 37 ≤ 280137542572022 := by decide +kernel

theorem rows22000E_75 : rowsJD 59 60 37 48 ≤ 281276809532853 := by decide +kernel

theorem rows22000E_76 : rowsJD 59 60 48 55 ≤ 152887666365989 := by decide +kernel

theorem rows22000E_77 : rowsJD 59 60 55 59 ≤ 73842668057854 := by decide +kernel

theorem rows22000E_78 : rowsJD 59 60 59 272 ≤ 17578414545680 := by decide +kernel

theorem rows22000E_79 : rowsJD 60 61 0 37 ≤ 277153349184671 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_70
#print axioms SieveDeep.rows22000E_79
