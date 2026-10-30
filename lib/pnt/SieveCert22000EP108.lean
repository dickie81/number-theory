/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1070–1079 of 1136

File 108 of 114: the parts `rows22000E_1070` … `rows22000E_1079` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 255 s of the kernel: row 210 columns 0–56, row 210 columns 57–271,
row 211 columns 0–56, row 211 columns 57–271, row 212 columns 0–55, row 212 columns 56–271, row 213 columns 0–55,
row 213 columns 56–271, row 214 columns 0–73, row 214 columns 74–271), each a sum of the costs (`rowsJD`) at most
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

theorem rows22000E_1070 : rowsJD 210 211 0 57 ≤ 579535137373168 := by decide +kernel

theorem rows22000E_1071 : rowsJD 210 211 57 272 ≤ 8644751413704439 := by decide +kernel

theorem rows22000E_1072 : rowsJD 211 212 0 57 ≤ 587710143295638 := by decide +kernel

theorem rows22000E_1073 : rowsJD 211 212 57 272 ≤ 8752963828998488 := by decide +kernel

theorem rows22000E_1074 : rowsJD 212 213 0 56 ≤ 544171290147655 := by decide +kernel

theorem rows22000E_1075 : rowsJD 212 213 56 272 ≤ 8819270464807385 := by decide +kernel

theorem rows22000E_1076 : rowsJD 213 214 0 56 ≤ 676435783611241 := by decide +kernel

theorem rows22000E_1077 : rowsJD 213 214 56 272 ≤ 8939577810876821 := by decide +kernel

theorem rows22000E_1078 : rowsJD 214 215 0 74 ≤ 737860937079239 := by decide +kernel

theorem rows22000E_1079 : rowsJD 214 215 74 272 ≤ 8955418004802020 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1070
#print axioms SieveDeep.rows22000E_1079
