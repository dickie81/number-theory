/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 310–319 of 1136

File 32 of 114: the parts `rows22000E_310` … `rows22000E_319` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 259 s of the kernel: row 93 columns 38–48, row 93 columns 49–58,
row 93 columns 59–69, row 93 columns 70–78, row 93 columns 79–84, row 93 columns 85–89, row 93 columns 90–92, row 93
columns 93–271, row 94 columns 0–37, row 94 columns 38–48), each a sum of the costs (`rowsJD`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_310 : rowsJD 93 94 38 49 ≤ 119341759990080 := by decide +kernel

theorem rows22000E_311 : rowsJD 93 94 49 59 ≤ 125197304076539 := by decide +kernel

theorem rows22000E_312 : rowsJD 93 94 59 70 ≤ 111465098293005 := by decide +kernel

theorem rows22000E_313 : rowsJD 93 94 70 79 ≤ 50616374854032 := by decide +kernel

theorem rows22000E_314 : rowsJD 93 94 79 85 ≤ 23622693634685 := by decide +kernel

theorem rows22000E_315 : rowsJD 93 94 85 90 ≤ 53075926146399 := by decide +kernel

theorem rows22000E_316 : rowsJD 93 94 90 93 ≤ 78657603131674 := by decide +kernel

theorem rows22000E_317 : rowsJD 93 94 93 272 ≤ 34377816128259 := by decide +kernel

theorem rows22000E_318 : rowsJD 94 95 0 38 ≤ 164346304389088 := by decide +kernel

theorem rows22000E_319 : rowsJD 94 95 38 49 ≤ 121443490407293 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_310
#print axioms SieveDeep.rows22000E_319
