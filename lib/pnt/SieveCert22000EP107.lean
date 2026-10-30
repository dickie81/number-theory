/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1060–1069 of 1136

File 107 of 114: the parts `rows22000E_1060` … `rows22000E_1069` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 234 s of the kernel: row 205 columns 132–271, row 206 columns
0–58, row 206 columns 59–132, row 206 columns 133–271, row 207 columns 0–58, row 207 columns 59–271, row 208 columns
0–57, row 208 columns 58–271, row 209 columns 0–57, row 209 columns 58–271), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_1060 : rowsJD 205 206 132 272 ≤ 2635522256493395 := by decide +kernel

theorem rows22000E_1061 : rowsJD 206 207 0 59 ≤ 537326137578419 := by decide +kernel

theorem rows22000E_1062 : rowsJD 206 207 59 133 ≤ 5885108477352110 := by decide +kernel

theorem rows22000E_1063 : rowsJD 206 207 133 272 ≤ 2449241101524779 := by decide +kernel

theorem rows22000E_1064 : rowsJD 207 208 0 59 ≤ 602505954354292 := by decide +kernel

theorem rows22000E_1065 : rowsJD 207 208 59 272 ≤ 8433343285207082 := by decide +kernel

theorem rows22000E_1066 : rowsJD 208 209 0 58 ≤ 624672042446022 := by decide +kernel

theorem rows22000E_1067 : rowsJD 208 209 58 272 ≤ 8495310234108595 := by decide +kernel

theorem rows22000E_1068 : rowsJD 209 210 0 58 ≤ 640937536376736 := by decide +kernel

theorem rows22000E_1069 : rowsJD 209 210 58 272 ≤ 8594800573493704 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1060
#print axioms SieveDeep.rows22000E_1069
