/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 150–159 of 1136

File 16 of 114: the parts `rows22000E_150` … `rows22000E_159` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 255 s of the kernel: row 72 columns 0–36, row 72 columns 37–47,
row 72 columns 48–54, row 72 columns 55–59, row 72 columns 60–64, row 72 columns 65–70, row 72 columns 71–271, row
73 columns 0–36, row 73 columns 37–47, row 73 columns 48–54), each a sum of the costs (`rowsJD`) at most its bound,
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

theorem rows22000E_150 : rowsJD 72 73 0 37 ≤ 243477386502458 := by decide +kernel

theorem rows22000E_151 : rowsJD 72 73 37 48 ≤ 183553478060696 := by decide +kernel

theorem rows22000E_152 : rowsJD 72 73 48 55 ≤ 89692655628742 := by decide +kernel

theorem rows22000E_153 : rowsJD 72 73 55 60 ≤ 62921391461268 := by decide +kernel

theorem rows22000E_154 : rowsJD 72 73 60 65 ≤ 60867925679216 := by decide +kernel

theorem rows22000E_155 : rowsJD 72 73 65 71 ≤ 73200731934118 := by decide +kernel

theorem rows22000E_156 : rowsJD 72 73 71 272 ≤ 32725357462818 := by decide +kernel

theorem rows22000E_157 : rowsJD 73 74 0 37 ≤ 240743790903257 := by decide +kernel

theorem rows22000E_158 : rowsJD 73 74 37 48 ≤ 176381487998824 := by decide +kernel

theorem rows22000E_159 : rowsJD 73 74 48 55 ≤ 87957575807884 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_150
#print axioms SieveDeep.rows22000E_159
