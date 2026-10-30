/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 250–259 of 1136

File 26 of 114: the parts `rows22000E_250` … `rows22000E_259` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 261 s of the kernel: row 85 columns 73–78, row 85 columns 79–83,
row 85 columns 84–271, row 86 columns 0–37, row 86 columns 38–48, row 86 columns 49–55, row 86 columns 56–64, row 86
columns 65–72, row 86 columns 73–79, row 86 columns 80–84), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_250 : rowsJD 85 86 73 79 ≤ 63553561888735 := by decide +kernel

theorem rows22000E_251 : rowsJD 85 86 79 84 ≤ 73352542659745 := by decide +kernel

theorem rows22000E_252 : rowsJD 85 86 84 272 ≤ 27009146794255 := by decide +kernel

theorem rows22000E_253 : rowsJD 86 87 0 38 ≤ 202877351668728 := by decide +kernel

theorem rows22000E_254 : rowsJD 86 87 38 49 ≤ 117592834343848 := by decide +kernel

theorem rows22000E_255 : rowsJD 86 87 49 56 ≤ 96053896527984 := by decide +kernel

theorem rows22000E_256 : rowsJD 86 87 56 65 ≤ 106792944696431 := by decide +kernel

theorem rows22000E_257 : rowsJD 86 87 65 73 ≤ 85327260255969 := by decide +kernel

theorem rows22000E_258 : rowsJD 86 87 73 80 ≤ 68778259811843 := by decide +kernel

theorem rows22000E_259 : rowsJD 86 87 80 85 ≤ 59340767681260 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_250
#print axioms SieveDeep.rows22000E_259
