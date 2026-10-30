/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 180–189 of 1136

File 19 of 114: the parts `rows22000E_180` … `rows22000E_189` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 271 s of the kernel: row 76 columns 49–55, row 76 columns 56–61,
row 76 columns 62–69, row 76 columns 70–74, row 76 columns 75–271, row 77 columns 0–36, row 77 columns 37–48, row 77
columns 49–55, row 77 columns 56–61, row 77 columns 62–69), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_180 : rowsJD 76 77 49 56 ≤ 85283329593886 := by decide +kernel

theorem rows22000E_181 : rowsJD 76 77 56 62 ≤ 75421818675590 := by decide +kernel

theorem rows22000E_182 : rowsJD 76 77 62 70 ≤ 97188757127421 := by decide +kernel

theorem rows22000E_183 : rowsJD 76 77 70 75 ≤ 74467945811382 := by decide +kernel

theorem rows22000E_184 : rowsJD 76 77 75 272 ≤ 37516234397422 := by decide +kernel

theorem rows22000E_185 : rowsJD 77 78 0 37 ≤ 228359057134035 := by decide +kernel

theorem rows22000E_186 : rowsJD 77 78 37 49 ≤ 161831144054200 := by decide +kernel

theorem rows22000E_187 : rowsJD 77 78 49 56 ≤ 84914993130102 := by decide +kernel

theorem rows22000E_188 : rowsJD 77 78 56 62 ≤ 75144872576640 := by decide +kernel

theorem rows22000E_189 : rowsJD 77 78 62 70 ≤ 97336828723337 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_180
#print axioms SieveDeep.rows22000E_189
