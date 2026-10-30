/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 760–769 of 1136

File 77 of 114: the parts `rows22000E_760` … `rows22000E_769` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 283 s of the kernel: row 147 columns 97–103, row 147 columns
104–110, row 147 columns 111–271, row 148 columns 0–47, row 148 columns 48–59, row 148 columns 60–88, row 148
columns 89–96, row 148 columns 97–103, row 148 columns 104–109, row 148 columns 110–119), each a sum of the costs
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

theorem rows22000E_760 : rowsJD 147 148 97 104 ≤ 416646441338230 := by decide +kernel

theorem rows22000E_761 : rowsJD 147 148 104 111 ≤ 424737629301170 := by decide +kernel

theorem rows22000E_762 : rowsJD 147 148 111 272 ≤ 1754123922501642 := by decide +kernel

theorem rows22000E_763 : rowsJD 148 149 0 48 ≤ 51739600454695 := by decide +kernel

theorem rows22000E_764 : rowsJD 148 149 48 60 ≤ 17942863850377 := by decide +kernel

theorem rows22000E_765 : rowsJD 148 149 60 89 ≤ 313161858222359 := by decide +kernel

theorem rows22000E_766 : rowsJD 148 149 89 97 ≤ 502963870425018 := by decide +kernel

theorem rows22000E_767 : rowsJD 148 149 97 104 ≤ 422316357915763 := by decide +kernel

theorem rows22000E_768 : rowsJD 148 149 104 110 ≤ 379185273984811 := by decide +kernel

theorem rows22000E_769 : rowsJD 148 149 110 120 ≤ 821499384948074 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_760
#print axioms SieveDeep.rows22000E_769
