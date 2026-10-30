/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 160–169 of 1136

File 17 of 114: the parts `rows22000E_160` … `rows22000E_169` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 251 s of the kernel: row 73 columns 55–59, row 73 columns 60–65,
row 73 columns 66–71, row 73 columns 72–271, row 74 columns 0–36, row 74 columns 37–47, row 74 columns 48–54, row 74
columns 55–59, row 74 columns 60–65, row 74 columns 66–71), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_160 : rowsJD 73 74 55 60 ≤ 62791177180827 := by decide +kernel

theorem rows22000E_161 : rowsJD 73 74 60 66 ≤ 71584270697710 := by decide +kernel

theorem rows22000E_162 : rowsJD 73 74 66 72 ≤ 77759281433929 := by decide +kernel

theorem rows22000E_163 : rowsJD 73 74 72 272 ≤ 34764118625038 := by decide +kernel

theorem rows22000E_164 : rowsJD 74 75 0 37 ≤ 237865521406494 := by decide +kernel

theorem rows22000E_165 : rowsJD 74 75 37 48 ≤ 169464308893629 := by decide +kernel

theorem rows22000E_166 : rowsJD 74 75 48 55 ≤ 86807639362386 := by decide +kernel

theorem rows22000E_167 : rowsJD 74 75 55 60 ≤ 63087096894504 := by decide +kernel

theorem rows22000E_168 : rowsJD 74 75 60 66 ≤ 71506457542225 := by decide +kernel

theorem rows22000E_169 : rowsJD 74 75 66 72 ≤ 77924998679062 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_160
#print axioms SieveDeep.rows22000E_169
