/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 390–399 of 1136

File 40 of 114: the parts `rows22000E_390` … `rows22000E_399` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 252 s of the kernel: row 101 columns 74–80, row 101 columns 81–86,
row 101 columns 87–90, row 101 columns 91–94, row 101 columns 95–97, row 101 columns 98–100, row 101 columns
101–271, row 102 columns 0–38, row 102 columns 39–51, row 102 columns 52–65), each a sum of the costs (`rowsJD`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_390 : rowsJD 101 102 74 81 ≤ 30749122065608 := by decide +kernel

theorem rows22000E_391 : rowsJD 101 102 81 87 ≤ 22184802634400 := by decide +kernel

theorem rows22000E_392 : rowsJD 101 102 87 91 ≤ 48631686637646 := by decide +kernel

theorem rows22000E_393 : rowsJD 101 102 91 95 ≤ 100888655027788 := by decide +kernel

theorem rows22000E_394 : rowsJD 101 102 95 98 ≤ 116959552094206 := by decide +kernel

theorem rows22000E_395 : rowsJD 101 102 98 101 ≤ 157044291384299 := by decide +kernel

theorem rows22000E_396 : rowsJD 101 102 101 272 ≤ 61240436727232 := by decide +kernel

theorem rows22000E_397 : rowsJD 102 103 0 39 ≤ 151623399849142 := by decide +kernel

theorem rows22000E_398 : rowsJD 102 103 39 52 ≤ 179802982463585 := by decide +kernel

theorem rows22000E_399 : rowsJD 102 103 52 66 ≤ 112967674411833 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_390
#print axioms SieveDeep.rows22000E_399
