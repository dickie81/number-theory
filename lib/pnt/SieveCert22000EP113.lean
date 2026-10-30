/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1120–1129 of 1136

File 113 of 114: the parts `rows22000E_1120` … `rows22000E_1129` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 267 s of the kernel: rows 256–256, rows 257–257, rows 258–258,
rows 259–259, rows 260–260, rows 261–261, rows 262–262, rows 263–263, rows 264–264, rows 265–265), each a sum of the
costs (`rowsJD`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_1120 : rowsJD 256 257 0 272 ≤ 13480289986803563 := by decide +kernel

theorem rows22000E_1121 : rowsJD 257 258 0 272 ≤ 13537734514421056 := by decide +kernel

theorem rows22000E_1122 : rowsJD 258 259 0 272 ≤ 13473974866657161 := by decide +kernel

theorem rows22000E_1123 : rowsJD 259 260 0 272 ≤ 13505386342402007 := by decide +kernel

theorem rows22000E_1124 : rowsJD 260 261 0 272 ≤ 13420365538005945 := by decide +kernel

theorem rows22000E_1125 : rowsJD 261 262 0 272 ≤ 13498548400386357 := by decide +kernel

theorem rows22000E_1126 : rowsJD 262 263 0 272 ≤ 13482751116335803 := by decide +kernel

theorem rows22000E_1127 : rowsJD 263 264 0 272 ≤ 13610546038084796 := by decide +kernel

theorem rows22000E_1128 : rowsJD 264 265 0 272 ≤ 13683474405311120 := by decide +kernel

theorem rows22000E_1129 : rowsJD 265 266 0 272 ≤ 13668711857135736 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1120
#print axioms SieveDeep.rows22000E_1129
