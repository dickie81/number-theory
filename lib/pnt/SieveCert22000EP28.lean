/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 270–279 of 1136

File 28 of 114: the parts `rows22000E_270` … `rows22000E_279` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 267 s of the kernel: row 88 columns 38–48, row 88 columns 49–56,
row 88 columns 57–66, row 88 columns 67–74, row 88 columns 75–81, row 88 columns 82–87, row 88 columns 88–271, row
89 columns 0–37, row 89 columns 38–48, row 89 columns 49–56), each a sum of the costs (`rowsJD`) at most its bound,
by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_270 : rowsJD 88 89 38 49 ≤ 116013937190990 := by decide +kernel

theorem rows22000E_271 : rowsJD 88 89 49 57 ≤ 109627366010732 := by decide +kernel

theorem rows22000E_272 : rowsJD 88 89 57 67 ≤ 119215008965475 := by decide +kernel

theorem rows22000E_273 : rowsJD 88 89 67 75 ≤ 70769618803912 := by decide +kernel

theorem rows22000E_274 : rowsJD 88 89 75 82 ≤ 56273817289108 := by decide +kernel

theorem rows22000E_275 : rowsJD 88 89 82 88 ≤ 42782562609416 := by decide +kernel

theorem rows22000E_276 : rowsJD 88 89 88 272 ≤ 12753485783731 := by decide +kernel

theorem rows22000E_277 : rowsJD 89 90 0 38 ≤ 188171951306795 := by decide +kernel

theorem rows22000E_278 : rowsJD 89 90 38 49 ≤ 115583155467156 := by decide +kernel

theorem rows22000E_279 : rowsJD 89 90 49 57 ≤ 108944759282729 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_270
#print axioms SieveDeep.rows22000E_279
