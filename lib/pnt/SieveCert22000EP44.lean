/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 430–439 of 1136

File 44 of 114: the parts `rows22000E_430` … `rows22000E_439` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 284 s of the kernel: row 105 columns 0–38, row 105 columns 39–52,
row 105 columns 53–66, row 105 columns 67–74, row 105 columns 75–82, row 105 columns 83–88, row 105 columns 89–93,
row 105 columns 94–97, row 105 columns 98–101, row 105 columns 102–104), each a sum of the costs (`rowsJD`) at most
its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_430 : rowsJD 105 106 0 39 ≤ 140986688908227 := by decide +kernel

theorem rows22000E_431 : rowsJD 105 106 39 53 ≤ 165782159863424 := by decide +kernel

theorem rows22000E_432 : rowsJD 105 106 53 67 ≤ 110821755071714 := by decide +kernel

theorem rows22000E_433 : rowsJD 105 106 67 75 ≤ 53629803940868 := by decide +kernel

theorem rows22000E_434 : rowsJD 105 106 75 83 ≤ 26220496746671 := by decide +kernel

theorem rows22000E_435 : rowsJD 105 106 83 89 ≤ 43783296077287 := by decide +kernel

theorem rows22000E_436 : rowsJD 105 106 89 94 ≤ 81329090441044 := by decide +kernel

theorem rows22000E_437 : rowsJD 105 106 94 98 ≤ 125769815677314 := by decide +kernel

theorem rows22000E_438 : rowsJD 105 106 98 102 ≤ 182717494024283 := by decide +kernel

theorem rows22000E_439 : rowsJD 105 106 102 105 ≤ 180195844724330 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_430
#print axioms SieveDeep.rows22000E_439
