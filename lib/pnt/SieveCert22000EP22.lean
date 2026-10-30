/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 210–219 of 1136

File 22 of 114: the parts `rows22000E_210` … `rows22000E_219` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 254 s of the kernel: row 80 columns 63–70, row 80 columns 71–75,
row 80 columns 76–79, row 80 columns 80–271, row 81 columns 0–36, row 81 columns 37–48, row 81 columns 49–55, row 81
columns 56–62, row 81 columns 63–70, row 81 columns 71–76), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_210 : rowsJD 80 81 63 71 ≤ 96240710681626 := by decide +kernel

theorem rows22000E_211 : rowsJD 80 81 71 76 ≤ 65719201898319 := by decide +kernel

theorem rows22000E_212 : rowsJD 80 81 76 80 ≤ 74578746706239 := by decide +kernel

theorem rows22000E_213 : rowsJD 80 81 80 272 ≤ 24417389752377 := by decide +kernel

theorem rows22000E_214 : rowsJD 81 82 0 37 ≤ 213835420175857 := by decide +kernel

theorem rows22000E_215 : rowsJD 81 82 37 49 ≤ 141361907969564 := by decide +kernel

theorem rows22000E_216 : rowsJD 81 82 49 56 ≤ 88677809700517 := by decide +kernel

theorem rows22000E_217 : rowsJD 81 82 56 63 ≤ 87398846573192 := by decide +kernel

theorem rows22000E_218 : rowsJD 81 82 63 71 ≤ 94975068777111 := by decide +kernel

theorem rows22000E_219 : rowsJD 81 82 71 77 ≤ 77610460258482 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_210
#print axioms SieveDeep.rows22000E_219
