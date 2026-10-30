/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 680–689 of 1136

File 69 of 114: the parts `rows22000E_680` … `rows22000E_689` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 267 s of the kernel: row 136 columns 48–61, row 136 columns 62–72,
row 136 columns 73–98, row 136 columns 99–106, row 136 columns 107–121, row 136 columns 122–271, row 137 columns
0–47, row 137 columns 48–61, row 137 columns 62–72, row 137 columns 73–98), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_680 : rowsJD 136 137 48 62 ≤ 48280706020194 := by decide +kernel

theorem rows22000E_681 : rowsJD 136 137 62 73 ≤ 115557848909373 := by decide +kernel

theorem rows22000E_682 : rowsJD 136 137 73 99 ≤ 260224384933286 := by decide +kernel

theorem rows22000E_683 : rowsJD 136 137 99 107 ≤ 315981303245195 := by decide +kernel

theorem rows22000E_684 : rowsJD 136 137 107 122 ≤ 1049742946283559 := by decide +kernel

theorem rows22000E_685 : rowsJD 136 137 122 272 ≤ 1252641100526544 := by decide +kernel

theorem rows22000E_686 : rowsJD 137 138 0 48 ≤ 87511745310777 := by decide +kernel

theorem rows22000E_687 : rowsJD 137 138 48 62 ≤ 42504336876688 := by decide +kernel

theorem rows22000E_688 : rowsJD 137 138 62 73 ≤ 114689834954002 := by decide +kernel

theorem rows22000E_689 : rowsJD 137 138 73 99 ≤ 227904252040376 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_680
#print axioms SieveDeep.rows22000E_689
