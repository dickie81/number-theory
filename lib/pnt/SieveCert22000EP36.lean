/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 350–359 of 1136

File 36 of 114: the parts `rows22000E_350` … `rows22000E_359` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 252 s of the kernel: row 97 columns 74–80, row 97 columns 81–86,
row 97 columns 87–90, row 97 columns 91–93, row 97 columns 94–96, row 97 columns 97–271, row 98 columns 0–38, row 98
columns 39–49, row 98 columns 50–62, row 98 columns 63–72), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_350 : rowsJD 97 98 74 81 ≤ 34448637295626 := by decide +kernel

theorem rows22000E_351 : rowsJD 97 98 81 87 ≤ 20652350472950 := by decide +kernel

theorem rows22000E_352 : rowsJD 97 98 87 91 ≤ 56677784133399 := by decide +kernel

theorem rows22000E_353 : rowsJD 97 98 91 94 ≤ 79465982447744 := by decide +kernel

theorem rows22000E_354 : rowsJD 97 98 94 97 ≤ 115354136003604 := by decide +kernel

theorem rows22000E_355 : rowsJD 97 98 97 272 ≤ 47429325524629 := by decide +kernel

theorem rows22000E_356 : rowsJD 98 99 0 39 ≤ 154046866930689 := by decide +kernel

theorem rows22000E_357 : rowsJD 98 99 39 50 ≤ 136775885433036 := by decide +kernel

theorem rows22000E_358 : rowsJD 98 99 50 63 ≤ 126545821197760 := by decide +kernel

theorem rows22000E_359 : rowsJD 98 99 63 73 ≤ 72618435928634 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_350
#print axioms SieveDeep.rows22000E_359
