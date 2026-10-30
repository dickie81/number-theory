/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1100–1109 of 1136

File 111 of 114: the parts `rows22000E_1100` … `rows22000E_1109` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 239 s of the kernel: row 225 columns 0–77, row 225 columns 78–271,
row 226 columns 0–78, row 226 columns 79–271, row 227 columns 0–78, row 227 columns 79–271, row 228 columns 0–75,
row 228 columns 76–271, row 229 columns 0–70, row 229 columns 71–271), each a sum of the costs (`rowsJD`) at most
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

theorem rows22000E_1100 : rowsJD 225 226 0 78 ≤ 3368896631499261 := by decide +kernel

theorem rows22000E_1101 : rowsJD 225 226 78 272 ≤ 7684178189318813 := by decide +kernel

theorem rows22000E_1102 : rowsJD 226 227 0 79 ≤ 3682326280198484 := by decide +kernel

theorem rows22000E_1103 : rowsJD 226 227 79 272 ≤ 7427040764717981 := by decide +kernel

theorem rows22000E_1104 : rowsJD 227 228 0 79 ≤ 3845208629016134 := by decide +kernel

theorem rows22000E_1105 : rowsJD 227 228 79 272 ≤ 7421584119405059 := by decide +kernel

theorem rows22000E_1106 : rowsJD 228 229 0 76 ≤ 3396806307197005 := by decide +kernel

theorem rows22000E_1107 : rowsJD 228 229 76 272 ≤ 7795513948139570 := by decide +kernel

theorem rows22000E_1108 : rowsJD 229 230 0 71 ≤ 2588262146730376 := by decide +kernel

theorem rows22000E_1109 : rowsJD 229 230 71 272 ≤ 8653047377406579 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1100
#print axioms SieveDeep.rows22000E_1109
