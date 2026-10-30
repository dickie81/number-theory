/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 290–299 of 1136

File 30 of 114: the parts `rows22000E_290` … `rows22000E_299` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 271 s of the kernel: row 90 columns 76–82, row 90 columns 83–87,
row 90 columns 88–271, row 91 columns 0–37, row 91 columns 38–48, row 91 columns 49–57, row 91 columns 58–67, row 91
columns 68–76, row 91 columns 77–83, row 91 columns 84–88), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_290 : rowsJD 90 91 76 83 ≤ 41303939679404 := by decide +kernel

theorem rows22000E_291 : rowsJD 90 91 83 88 ≤ 31662503771360 := by decide +kernel

theorem rows22000E_292 : rowsJD 90 91 88 272 ≤ 49817906632872 := by decide +kernel

theorem rows22000E_293 : rowsJD 91 92 0 38 ≤ 178468529552608 := by decide +kernel

theorem rows22000E_294 : rowsJD 91 92 38 49 ≤ 116774619668629 := by decide +kernel

theorem rows22000E_295 : rowsJD 91 92 49 58 ≤ 119321413164397 := by decide +kernel

theorem rows22000E_296 : rowsJD 91 92 58 68 ≤ 115848351727207 := by decide +kernel

theorem rows22000E_297 : rowsJD 91 92 68 77 ≤ 59309195089279 := by decide +kernel

theorem rows22000E_298 : rowsJD 91 92 77 84 ≤ 34978284276841 := by decide +kernel

theorem rows22000E_299 : rowsJD 91 92 84 89 ≤ 40049897140649 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_290
#print axioms SieveDeep.rows22000E_299
