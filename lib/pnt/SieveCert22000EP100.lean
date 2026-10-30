/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 990–999 of 1136

File 100 of 114: the parts `rows22000E_990` … `rows22000E_999` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 256 s of the kernel: row 183 columns 81–109, row 183 columns
110–271, row 184 columns 0–69, row 184 columns 70–80, row 184 columns 81–111, row 184 columns 112–271, row 185
columns 0–70, row 185 columns 71–80, row 185 columns 81–113, row 185 columns 114–271), each a sum of the costs
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

theorem rows22000E_990 : rowsJD 183 184 81 110 ≤ 907466382255639 := by decide +kernel

theorem rows22000E_991 : rowsJD 183 184 110 272 ≤ 5727179009360201 := by decide +kernel

theorem rows22000E_992 : rowsJD 184 185 0 70 ≤ 198590296587760 := by decide +kernel

theorem rows22000E_993 : rowsJD 184 185 70 81 ≤ 374204721466326 := by decide +kernel

theorem rows22000E_994 : rowsJD 184 185 81 112 ≤ 1134396092299668 := by decide +kernel

theorem rows22000E_995 : rowsJD 184 185 112 272 ≤ 5461820708353961 := by decide +kernel

theorem rows22000E_996 : rowsJD 185 186 0 71 ≤ 252366606405308 := by decide +kernel

theorem rows22000E_997 : rowsJD 185 186 71 81 ≤ 356631054027374 := by decide +kernel

theorem rows22000E_998 : rowsJD 185 186 81 114 ≤ 1348704970289865 := by decide +kernel

theorem rows22000E_999 : rowsJD 185 186 114 272 ≤ 5284640409274115 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_990
#print axioms SieveDeep.rows22000E_999
