/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 280–289 of 1136

File 29 of 114: the parts `rows22000E_280` … `rows22000E_289` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 266 s of the kernel: row 89 columns 57–66, row 89 columns 67–75,
row 89 columns 76–82, row 89 columns 83–87, row 89 columns 88–271, row 90 columns 0–37, row 90 columns 38–48, row 90
columns 49–56, row 90 columns 57–66, row 90 columns 67–75), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_280 : rowsJD 89 90 57 67 ≤ 118970732979804 := by decide +kernel

theorem rows22000E_281 : rowsJD 89 90 67 76 ≤ 73539194441262 := by decide +kernel

theorem rows22000E_282 : rowsJD 89 90 76 83 ≤ 45490911886080 := by decide +kernel

theorem rows22000E_283 : rowsJD 89 90 83 88 ≤ 32113156735208 := by decide +kernel

theorem rows22000E_284 : rowsJD 89 90 88 272 ≤ 25677216851786 := by decide +kernel

theorem rows22000E_285 : rowsJD 90 91 0 38 ≤ 183444991011589 := by decide +kernel

theorem rows22000E_286 : rowsJD 90 91 38 49 ≤ 116013254392320 := by decide +kernel

theorem rows22000E_287 : rowsJD 90 91 49 57 ≤ 108936726100849 := by decide +kernel

theorem rows22000E_288 : rowsJD 90 91 57 67 ≤ 118462892449008 := by decide +kernel

theorem rows22000E_289 : rowsJD 90 91 67 76 ≤ 68100911979294 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_280
#print axioms SieveDeep.rows22000E_289
