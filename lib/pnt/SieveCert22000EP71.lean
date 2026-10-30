/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 700–709 of 1136

File 71 of 114: the parts `rows22000E_700` … `rows22000E_709` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 262 s of the kernel: row 139 columns 0–47, row 139 columns 48–61,
row 139 columns 62–72, row 139 columns 73–99, row 139 columns 100–108, row 139 columns 109–128, row 139 columns
129–271, row 140 columns 0–47, row 140 columns 48–61, row 140 columns 62–72), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_700 : rowsJD 139 140 0 48 ≤ 79893558930029 := by decide +kernel

theorem rows22000E_701 : rowsJD 139 140 48 62 ≤ 33576471675819 := by decide +kernel

theorem rows22000E_702 : rowsJD 139 140 62 73 ≤ 137039085315929 := by decide +kernel

theorem rows22000E_703 : rowsJD 139 140 73 100 ≤ 233229735036925 := by decide +kernel

theorem rows22000E_704 : rowsJD 139 140 100 109 ≤ 340499059336290 := by decide +kernel

theorem rows22000E_705 : rowsJD 139 140 109 129 ≤ 1618195343230747 := by decide +kernel

theorem rows22000E_706 : rowsJD 139 140 129 272 ≤ 205739640071740 := by decide +kernel

theorem rows22000E_707 : rowsJD 140 141 0 48 ≤ 76649523651903 := by decide +kernel

theorem rows22000E_708 : rowsJD 140 141 48 62 ≤ 30368206196261 := by decide +kernel

theorem rows22000E_709 : rowsJD 140 141 62 73 ≤ 164124021423209 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_700
#print axioms SieveDeep.rows22000E_709
