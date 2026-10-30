/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 260–269 of 1136

File 27 of 114: the parts `rows22000E_260` … `rows22000E_269` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 248 s of the kernel: row 86 columns 85–271, row 87 columns 0–37,
row 87 columns 38–48, row 87 columns 49–55, row 87 columns 56–65, row 87 columns 66–73, row 87 columns 74–80, row 87
columns 81–85, row 87 columns 86–271, row 88 columns 0–37), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_260 : rowsJD 86 87 85 272 ≤ 22725910166179 := by decide +kernel

theorem rows22000E_261 : rowsJD 87 88 0 38 ≤ 197890852662792 := by decide +kernel

theorem rows22000E_262 : rowsJD 87 88 38 49 ≤ 116714083527556 := by decide +kernel

theorem rows22000E_263 : rowsJD 87 88 49 56 ≤ 96847367484414 := by decide +kernel

theorem rows22000E_264 : rowsJD 87 88 56 66 ≤ 119196322393435 := by decide +kernel

theorem rows22000E_265 : rowsJD 87 88 66 74 ≤ 79354734931725 := by decide +kernel

theorem rows22000E_266 : rowsJD 87 88 74 81 ≤ 62606860369821 := by decide +kernel

theorem rows22000E_267 : rowsJD 87 88 81 86 ≤ 44782306700119 := by decide +kernel

theorem rows22000E_268 : rowsJD 87 88 86 272 ≤ 19404851438054 := by decide +kernel

theorem rows22000E_269 : rowsJD 88 89 0 38 ≤ 193053373366557 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_260
#print axioms SieveDeep.rows22000E_269
