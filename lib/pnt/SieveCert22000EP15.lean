/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 140–149 of 1136

File 15 of 114: the parts `rows22000E_140` … `rows22000E_149` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 253 s of the kernel: row 70 columns 55–59, row 70 columns 60–64,
row 70 columns 65–271, row 71 columns 0–36, row 71 columns 37–47, row 71 columns 48–54, row 71 columns 55–59, row 71
columns 60–64, row 71 columns 65–70, row 71 columns 71–271), each a sum of the costs (`rowsJD`) at most its bound,
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

theorem rows22000E_140 : rowsJD 70 71 55 60 ≤ 63749171767040 := by decide +kernel

theorem rows22000E_141 : rowsJD 70 71 60 65 ≤ 64948802938385 := by decide +kernel

theorem rows22000E_142 : rowsJD 70 71 65 272 ≤ 72668426365155 := by decide +kernel

theorem rows22000E_143 : rowsJD 71 72 0 37 ≤ 246027326875313 := by decide +kernel

theorem rows22000E_144 : rowsJD 71 72 37 48 ≤ 190747199808868 := by decide +kernel

theorem rows22000E_145 : rowsJD 71 72 48 55 ≤ 91346676356765 := by decide +kernel

theorem rows22000E_146 : rowsJD 71 72 55 60 ≤ 62900272511098 := by decide +kernel

theorem rows22000E_147 : rowsJD 71 72 60 65 ≤ 61958618513718 := by decide +kernel

theorem rows22000E_148 : rowsJD 71 72 65 71 ≤ 72556910535609 := by decide +kernel

theorem rows22000E_149 : rowsJD 71 72 71 272 ≤ 14816106130217 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_140
#print axioms SieveDeep.rows22000E_149
