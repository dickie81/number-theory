/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 90–99 of 1136

File 10 of 114: the parts `rows22000E_90` … `rows22000E_99` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 251 s of the kernel: row 62 columns 37–47, row 62 columns 48–54,
row 62 columns 55–58, row 62 columns 59–271, row 63 columns 0–36, row 63 columns 37–47, row 63 columns 48–54, row 63
columns 55–58, row 63 columns 59–62, row 63 columns 63–271), each a sum of the costs (`rowsJD`) at most its bound,
by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_90 : rowsJD 62 63 37 48 ≤ 259047624405043 := by decide +kernel

theorem rows22000E_91 : rowsJD 62 63 48 55 ≤ 132506289539167 := by decide +kernel

theorem rows22000E_92 : rowsJD 62 63 55 59 ≤ 64214939218695 := by decide +kernel

theorem rows22000E_93 : rowsJD 62 63 59 272 ≤ 65076174285674 := by decide +kernel

theorem rows22000E_94 : rowsJD 63 64 0 37 ≤ 269959152633557 := by decide +kernel

theorem rows22000E_95 : rowsJD 63 64 37 48 ≤ 251802113885844 := by decide +kernel

theorem rows22000E_96 : rowsJD 63 64 48 55 ≤ 126496008573907 := by decide +kernel

theorem rows22000E_97 : rowsJD 63 64 55 59 ≤ 61670323421788 := by decide +kernel

theorem rows22000E_98 : rowsJD 63 64 59 63 ≤ 63329627072945 := by decide +kernel

theorem rows22000E_99 : rowsJD 63 64 63 272 ≤ 18491641648741 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_90
#print axioms SieveDeep.rows22000E_99
