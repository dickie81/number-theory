/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 360–369 of 1136

File 37 of 114: the parts `rows22000E_360` … `rows22000E_369` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 266 s of the kernel: row 98 columns 73–80, row 98 columns 81–86,
row 98 columns 87–90, row 98 columns 91–93, row 98 columns 94–96, row 98 columns 97–271, row 99 columns 0–38, row 99
columns 39–49, row 99 columns 50–63, row 99 columns 64–73), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_360 : rowsJD 98 99 73 81 ≤ 41829596375465 := by decide +kernel

theorem rows22000E_361 : rowsJD 98 99 81 87 ≤ 19701817237674 := by decide +kernel

theorem rows22000E_362 : rowsJD 98 99 87 91 ≤ 54732945773276 := by decide +kernel

theorem rows22000E_363 : rowsJD 98 99 91 94 ≤ 77239268933263 := by decide +kernel

theorem rows22000E_364 : rowsJD 98 99 94 97 ≤ 113330890033591 := by decide +kernel

theorem rows22000E_365 : rowsJD 98 99 97 272 ≤ 99214379955261 := by decide +kernel

theorem rows22000E_366 : rowsJD 99 100 0 39 ≤ 151924581053762 := by decide +kernel

theorem rows22000E_367 : rowsJD 99 100 39 50 ≤ 142573363179613 := by decide +kernel

theorem rows22000E_368 : rowsJD 99 100 50 64 ≤ 128151185582662 := by decide +kernel

theorem rows22000E_369 : rowsJD 99 100 64 74 ≤ 73514733162989 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_360
#print axioms SieveDeep.rows22000E_369
