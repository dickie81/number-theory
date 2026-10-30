/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 320–329 of 1136

File 33 of 114: the parts `rows22000E_320` … `rows22000E_329` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 265 s of the kernel: row 94 columns 49–58, row 94 columns 59–69,
row 94 columns 70–78, row 94 columns 79–84, row 94 columns 85–89, row 94 columns 90–92, row 94 columns 93–271, row
95 columns 0–37, row 95 columns 38–48, row 95 columns 49–59), each a sum of the costs (`rowsJD`) at most its bound,
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

theorem rows22000E_320 : rowsJD 94 95 49 59 ≤ 122615204191902 := by decide +kernel

theorem rows22000E_321 : rowsJD 94 95 59 70 ≤ 106221016576117 := by decide +kernel

theorem rows22000E_322 : rowsJD 94 95 70 79 ≤ 50267823324167 := by decide +kernel

theorem rows22000E_323 : rowsJD 94 95 79 85 ≤ 21346451189105 := by decide +kernel

theorem rows22000E_324 : rowsJD 94 95 85 90 ≤ 52407325546924 := by decide +kernel

theorem rows22000E_325 : rowsJD 94 95 90 93 ≤ 76048327638851 := by decide +kernel

theorem rows22000E_326 : rowsJD 94 95 93 272 ≤ 71444641135718 := by decide +kernel

theorem rows22000E_327 : rowsJD 95 96 0 38 ≤ 159746109960076 := by decide +kernel

theorem rows22000E_328 : rowsJD 95 96 38 49 ≤ 123741158931297 := by decide +kernel

theorem rows22000E_329 : rowsJD 95 96 49 60 ≤ 129490636753592 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_320
#print axioms SieveDeep.rows22000E_329
