/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 220–229 of 1136

File 23 of 114: the parts `rows22000E_220` … `rows22000E_229` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 263 s of the kernel: row 81 columns 77–271, row 82 columns 0–36,
row 82 columns 37–47, row 82 columns 48–54, row 82 columns 55–61, row 82 columns 62–69, row 82 columns 70–75, row 82
columns 76–80, row 82 columns 81–271, row 83 columns 0–36), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_220 : rowsJD 81 82 77 272 ≤ 97792979740843 := by decide +kernel

theorem rows22000E_221 : rowsJD 82 83 0 37 ≤ 209940312460629 := by decide +kernel

theorem rows22000E_222 : rowsJD 82 83 37 48 ≤ 126040252468308 := by decide +kernel

theorem rows22000E_223 : rowsJD 82 83 48 55 ≤ 88705119614572 := by decide +kernel

theorem rows22000E_224 : rowsJD 82 83 55 62 ≤ 88765586948431 := by decide +kernel

theorem rows22000E_225 : rowsJD 82 83 62 70 ≤ 94995953468897 := by decide +kernel

theorem rows22000E_226 : rowsJD 82 83 70 76 ≤ 70529214515927 := by decide +kernel

theorem rows22000E_227 : rowsJD 82 83 76 81 ≤ 81670792372257 := by decide +kernel

theorem rows22000E_228 : rowsJD 82 83 81 272 ≤ 48323098012569 := by decide +kernel

theorem rows22000E_229 : rowsJD 83 84 0 37 ≤ 205607098484247 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_220
#print axioms SieveDeep.rows22000E_229
