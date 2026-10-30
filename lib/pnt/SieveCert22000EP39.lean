/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 380–389 of 1136

File 39 of 114: the parts `rows22000E_380` … `rows22000E_389` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 274 s of the kernel: row 100 columns 74–80, row 100 columns 81–86,
row 100 columns 87–90, row 100 columns 91–94, row 100 columns 95–97, row 100 columns 98–271, row 101 columns 0–38,
row 101 columns 39–50, row 101 columns 51–64, row 101 columns 65–73), each a sum of the costs (`rowsJD`) at most its
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

theorem rows22000E_380 : rowsJD 100 101 74 81 ≤ 33174195957486 := by decide +kernel

theorem rows22000E_381 : rowsJD 100 101 81 87 ≤ 20252935151361 := by decide +kernel

theorem rows22000E_382 : rowsJD 100 101 87 91 ≤ 50756382528518 := by decide +kernel

theorem rows22000E_383 : rowsJD 100 101 91 95 ≤ 105372515722488 := by decide +kernel

theorem rows22000E_384 : rowsJD 100 101 95 98 ≤ 120720790589420 := by decide +kernel

theorem rows22000E_385 : rowsJD 100 101 98 272 ≤ 162612455885910 := by decide +kernel

theorem rows22000E_386 : rowsJD 101 102 0 39 ≤ 150946924669141 := by decide +kernel

theorem rows22000E_387 : rowsJD 101 102 39 51 ≤ 165243781414164 := by decide +kernel

theorem rows22000E_388 : rowsJD 101 102 51 65 ≤ 116753049969080 := by decide +kernel

theorem rows22000E_389 : rowsJD 101 102 65 74 ≤ 67081290676590 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_380
#print axioms SieveDeep.rows22000E_389
