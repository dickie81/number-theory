/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 660–669 of 1136

File 67 of 114: the parts `rows22000E_660` … `rows22000E_669` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 278 s of the kernel: row 133 columns 62–72, row 133 columns 73–79,
row 133 columns 80–104, row 133 columns 105–113, row 133 columns 114–271, row 134 columns 0–47, row 134 columns
48–61, row 134 columns 62–72, row 134 columns 73–97, row 134 columns 98–105), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_660 : rowsJD 133 134 62 73 ≤ 103884331539020 := by decide +kernel

theorem rows22000E_661 : rowsJD 133 134 73 80 ≤ 304629978173208 := by decide +kernel

theorem rows22000E_662 : rowsJD 133 134 80 105 ≤ 286760727198714 := by decide +kernel

theorem rows22000E_663 : rowsJD 133 134 105 114 ≤ 404651258450493 := by decide +kernel

theorem rows22000E_664 : rowsJD 133 134 114 272 ≤ 2053430943168532 := by decide +kernel

theorem rows22000E_665 : rowsJD 134 135 0 48 ≤ 99377551540158 := by decide +kernel

theorem rows22000E_666 : rowsJD 134 135 48 62 ≤ 59149379940501 := by decide +kernel

theorem rows22000E_667 : rowsJD 134 135 62 73 ≤ 109092066770593 := by decide +kernel

theorem rows22000E_668 : rowsJD 134 135 73 98 ≤ 306941792717567 := by decide +kernel

theorem rows22000E_669 : rowsJD 134 135 98 106 ≤ 304661359069427 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_660
#print axioms SieveDeep.rows22000E_669
