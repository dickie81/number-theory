/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 450–459 of 1136

File 46 of 114: the parts `rows22000E_450` … `rows22000E_459` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 260 s of the kernel: row 106 columns 103–105, row 106 columns
106–271, row 107 columns 0–38, row 107 columns 39–53, row 107 columns 54–67, row 107 columns 68–75, row 107 columns
76–83, row 107 columns 84–89, row 107 columns 90–94, row 107 columns 95–98), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_450 : rowsJD 106 107 103 106 ≤ 186293226027542 := by decide +kernel

theorem rows22000E_451 : rowsJD 106 107 106 272 ≤ 72415501735084 := by decide +kernel

theorem rows22000E_452 : rowsJD 107 108 0 39 ≤ 131277019795506 := by decide +kernel

theorem rows22000E_453 : rowsJD 107 108 39 54 ≤ 152203710948477 := by decide +kernel

theorem rows22000E_454 : rowsJD 107 108 54 68 ≤ 108806681568399 := by decide +kernel

theorem rows22000E_455 : rowsJD 107 108 68 76 ≤ 44987658085783 := by decide +kernel

theorem rows22000E_456 : rowsJD 107 108 76 84 ≤ 30745256488817 := by decide +kernel

theorem rows22000E_457 : rowsJD 107 108 84 90 ≤ 46218391277358 := by decide +kernel

theorem rows22000E_458 : rowsJD 107 108 90 95 ≤ 88762988606058 := by decide +kernel

theorem rows22000E_459 : rowsJD 107 108 95 99 ≤ 126838354557322 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_450
#print axioms SieveDeep.rows22000E_459
