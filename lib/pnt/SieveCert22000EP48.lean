/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 470–479 of 1136

File 48 of 114: the parts `rows22000E_470` … `rows22000E_479` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 270 s of the kernel: row 108 columns 96–99, row 108 columns
100–103, row 108 columns 104–271, row 109 columns 0–39, row 109 columns 40–56, row 109 columns 57–68, row 109
columns 69–77, row 109 columns 78–85, row 109 columns 86–91, row 109 columns 92–96), each a sum of the costs
(`rowsJD`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_470 : rowsJD 108 109 96 100 ≤ 131624697277771 := by decide +kernel

theorem rows22000E_471 : rowsJD 108 109 100 104 ≤ 186346684460070 := by decide +kernel

theorem rows22000E_472 : rowsJD 108 109 104 272 ≤ 117660985033153 := by decide +kernel

theorem rows22000E_473 : rowsJD 109 110 0 40 ≤ 149379552381221 := by decide +kernel

theorem rows22000E_474 : rowsJD 109 110 40 57 ≤ 157151883355505 := by decide +kernel

theorem rows22000E_475 : rowsJD 109 110 57 69 ≤ 103795435812648 := by decide +kernel

theorem rows22000E_476 : rowsJD 109 110 69 78 ≤ 42979853332346 := by decide +kernel

theorem rows22000E_477 : rowsJD 109 110 78 86 ≤ 45700755945454 := by decide +kernel

theorem rows22000E_478 : rowsJD 109 110 86 92 ≤ 54022358082745 := by decide +kernel

theorem rows22000E_479 : rowsJD 109 110 92 97 ≤ 104097870886873 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_470
#print axioms SieveDeep.rows22000E_479
