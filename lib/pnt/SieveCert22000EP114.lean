/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1130–1135 of 1136

File 114 of 114: the parts `rows22000E_1130` … `rows22000E_1135` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (6 parts, predicted 146 s of the kernel: rows 266–266, rows 267–267, rows 268–268, rows
269–269, rows 270–270, rows 271–271), each a sum of the costs (`rowsJD`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

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

theorem rows22000E_1130 : rowsJD 266 267 0 272 ≤ 13501854915544660 := by decide +kernel

theorem rows22000E_1131 : rowsJD 267 268 0 272 ≤ 13387883569682495 := by decide +kernel

theorem rows22000E_1132 : rowsJD 268 269 0 272 ≤ 13113274700551893 := by decide +kernel

theorem rows22000E_1133 : rowsJD 269 270 0 272 ≤ 12890943179370461 := by decide +kernel

theorem rows22000E_1134 : rowsJD 270 271 0 272 ≤ 12509620190291290 := by decide +kernel

theorem rows22000E_1135 : rowsJD 271 272 0 272 ≤ 12655995233617478 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1130
#print axioms SieveDeep.rows22000E_1135
