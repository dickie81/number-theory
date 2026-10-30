/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 240–249 of 1136

File 25 of 114: the parts `rows22000E_240` … `rows22000E_249` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 265 s of the kernel: row 84 columns 56–64, row 84 columns 65–72,
row 84 columns 73–78, row 84 columns 79–83, row 84 columns 84–271, row 85 columns 0–37, row 85 columns 38–48, row 85
columns 49–55, row 85 columns 56–64, row 85 columns 65–72), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_240 : rowsJD 84 85 56 65 ≤ 109194794601291 := by decide +kernel

theorem rows22000E_241 : rowsJD 84 85 65 73 ≤ 88127318110894 := by decide +kernel

theorem rows22000E_242 : rowsJD 84 85 73 79 ≤ 69750286522182 := by decide +kernel

theorem rows22000E_243 : rowsJD 84 85 79 84 ≤ 86466028789088 := by decide +kernel

theorem rows22000E_244 : rowsJD 84 85 84 272 ≤ 19228485305455 := by decide +kernel

theorem rows22000E_245 : rowsJD 85 86 0 38 ≤ 207790827312381 := by decide +kernel

theorem rows22000E_246 : rowsJD 85 86 38 49 ≤ 118913628317889 := by decide +kernel

theorem rows22000E_247 : rowsJD 85 86 49 56 ≤ 94673224642582 := by decide +kernel

theorem rows22000E_248 : rowsJD 85 86 56 65 ≤ 107836970834089 := by decide +kernel

theorem rows22000E_249 : rowsJD 85 86 65 73 ≤ 86485776116933 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_240
#print axioms SieveDeep.rows22000E_249
