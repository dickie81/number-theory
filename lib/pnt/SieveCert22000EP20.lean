/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 190–199 of 1136

File 20 of 114: the parts `rows22000E_190` … `rows22000E_199` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 265 s of the kernel: row 77 columns 70–74, row 77 columns 75–271,
row 78 columns 0–36, row 78 columns 37–48, row 78 columns 49–55, row 78 columns 56–61, row 78 columns 62–69, row 78
columns 70–74, row 78 columns 75–271, row 79 columns 0–36), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_190 : rowsJD 77 78 70 75 ≤ 70932494639239 := by decide +kernel

theorem rows22000E_191 : rowsJD 77 78 75 272 ≤ 55719763946000 := by decide +kernel

theorem rows22000E_192 : rowsJD 78 79 0 37 ≤ 224953093953868 := by decide +kernel

theorem rows22000E_193 : rowsJD 78 79 37 49 ≤ 155789278219689 := by decide +kernel

theorem rows22000E_194 : rowsJD 78 79 49 56 ≤ 85154590621096 := by decide +kernel

theorem rows22000E_195 : rowsJD 78 79 56 62 ≤ 75444740823189 := by decide +kernel

theorem rows22000E_196 : rowsJD 78 79 62 70 ≤ 97391465023161 := by decide +kernel

theorem rows22000E_197 : rowsJD 78 79 70 75 ≤ 68051175410513 := by decide +kernel

theorem rows22000E_198 : rowsJD 78 79 75 272 ≤ 74834785620975 := by decide +kernel

theorem rows22000E_199 : rowsJD 79 80 0 37 ≤ 221342223609419 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_190
#print axioms SieveDeep.rows22000E_199
