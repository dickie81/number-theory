/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 410–419 of 1136

File 42 of 114: the parts `rows22000E_410` … `rows22000E_419` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 259 s of the kernel: row 103 columns 52–66, row 103 columns 67–74,
row 103 columns 75–82, row 103 columns 83–88, row 103 columns 89–92, row 103 columns 93–96, row 103 columns 97–99,
row 103 columns 100–102, row 103 columns 103–271, row 104 columns 0–38), each a sum of the costs (`rowsJD`) at most
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

theorem rows22000E_410 : rowsJD 103 104 52 67 ≤ 120075385808189 := by decide +kernel

theorem rows22000E_411 : rowsJD 103 104 67 75 ≤ 56799915124746 := by decide +kernel

theorem rows22000E_412 : rowsJD 103 104 75 83 ≤ 25003139371973 := by decide +kernel

theorem rows22000E_413 : rowsJD 103 104 83 89 ≤ 40934710470718 := by decide +kernel

theorem rows22000E_414 : rowsJD 103 104 89 93 ≤ 65247582291585 := by decide +kernel

theorem rows22000E_415 : rowsJD 103 104 93 97 ≤ 120795678050881 := by decide +kernel

theorem rows22000E_416 : rowsJD 103 104 97 100 ≤ 133083322756430 := by decide +kernel

theorem rows22000E_417 : rowsJD 103 104 100 103 ≤ 169282823673579 := by decide +kernel

theorem rows22000E_418 : rowsJD 103 104 103 272 ≤ 64672107917147 := by decide +kernel

theorem rows22000E_419 : rowsJD 104 105 0 39 ≤ 145557073431238 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_410
#print axioms SieveDeep.rows22000E_419
