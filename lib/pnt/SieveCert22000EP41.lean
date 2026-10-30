/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 400–409 of 1136

File 41 of 114: the parts `rows22000E_400` … `rows22000E_409` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 256 s of the kernel: row 102 columns 66–73, row 102 columns 74–80,
row 102 columns 81–86, row 102 columns 87–90, row 102 columns 91–94, row 102 columns 95–97, row 102 columns 98–100,
row 102 columns 101–271, row 103 columns 0–38, row 103 columns 39–51), each a sum of the costs (`rowsJD`) at most
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

theorem rows22000E_400 : rowsJD 102 103 66 74 ≤ 59454952899376 := by decide +kernel

theorem rows22000E_401 : rowsJD 102 103 74 81 ≤ 27952450190726 := by decide +kernel

theorem rows22000E_402 : rowsJD 102 103 81 87 ≤ 24780255074081 := by decide +kernel

theorem rows22000E_403 : rowsJD 102 103 87 91 ≤ 45836537921988 := by decide +kernel

theorem rows22000E_404 : rowsJD 102 103 91 95 ≤ 96489944240133 := by decide +kernel

theorem rows22000E_405 : rowsJD 102 103 95 98 ≤ 112406387817580 := by decide +kernel

theorem rows22000E_406 : rowsJD 102 103 98 101 ≤ 151710006795962 := by decide +kernel

theorem rows22000E_407 : rowsJD 102 103 101 272 ≤ 122670141018799 := by decide +kernel

theorem rows22000E_408 : rowsJD 103 104 0 39 ≤ 149830326212211 := by decide +kernel

theorem rows22000E_409 : rowsJD 103 104 39 52 ≤ 175969766624405 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_400
#print axioms SieveDeep.rows22000E_409
