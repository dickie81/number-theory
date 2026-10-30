/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1080–1089 of 1136

File 109 of 114: the parts `rows22000E_1080` … `rows22000E_1089` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 236 s of the kernel: row 215 columns 0–74, row 215 columns 75–271,
row 216 columns 0–76, row 216 columns 77–271, row 217 columns 0–75, row 217 columns 76–271, row 218 columns 0–75,
row 218 columns 76–271, row 219 columns 0–76, row 219 columns 77–271), each a sum of the costs (`rowsJD`) at most
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

theorem rows22000E_1080 : rowsJD 215 216 0 75 ≤ 1134300138094445 := by decide +kernel

theorem rows22000E_1081 : rowsJD 215 216 75 272 ≤ 8760947594577303 := by decide +kernel

theorem rows22000E_1082 : rowsJD 216 217 0 77 ≤ 1694941407209770 := by decide +kernel

theorem rows22000E_1083 : rowsJD 216 217 77 272 ≤ 8307526451305465 := by decide +kernel

theorem rows22000E_1084 : rowsJD 217 218 0 76 ≤ 1723430063447197 := by decide +kernel

theorem rows22000E_1085 : rowsJD 217 218 76 272 ≤ 8466915616590127 := by decide +kernel

theorem rows22000E_1086 : rowsJD 218 219 0 76 ≤ 1838403751005860 := by decide +kernel

theorem rows22000E_1087 : rowsJD 218 219 76 272 ≤ 8361616246636317 := by decide +kernel

theorem rows22000E_1088 : rowsJD 219 220 0 77 ≤ 2130534649670121 := by decide +kernel

theorem rows22000E_1089 : rowsJD 219 220 77 272 ≤ 8181042266400301 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1080
#print axioms SieveDeep.rows22000E_1089
