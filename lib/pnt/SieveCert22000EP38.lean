/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 370–379 of 1136

File 38 of 114: the parts `rows22000E_370` … `rows22000E_379` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 269 s of the kernel: row 99 columns 74–80, row 99 columns 81–86,
row 99 columns 87–90, row 99 columns 91–94, row 99 columns 95–97, row 99 columns 98–271, row 100 columns 0–38, row
100 columns 39–50, row 100 columns 51–64, row 100 columns 65–73), each a sum of the costs (`rowsJD`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_370 : rowsJD 99 100 74 81 ≤ 34276687576193 := by decide +kernel

theorem rows22000E_371 : rowsJD 99 100 81 87 ≤ 19756750079758 := by decide +kernel

theorem rows22000E_372 : rowsJD 99 100 87 91 ≤ 53047658166255 := by decide +kernel

theorem rows22000E_373 : rowsJD 99 100 91 95 ≤ 108890765607988 := by decide +kernel

theorem rows22000E_374 : rowsJD 99 100 95 98 ≤ 123782925382373 := by decide +kernel

theorem rows22000E_375 : rowsJD 99 100 98 272 ≤ 106387029238973 := by decide +kernel

theorem rows22000E_376 : rowsJD 100 101 0 39 ≤ 151001124430276 := by decide +kernel

theorem rows22000E_377 : rowsJD 100 101 39 51 ≤ 161048091679925 := by decide +kernel

theorem rows22000E_378 : rowsJD 100 101 51 65 ≤ 118002797686263 := by decide +kernel

theorem rows22000E_379 : rowsJD 100 101 65 74 ≤ 67380254568197 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_370
#print axioms SieveDeep.rows22000E_379
