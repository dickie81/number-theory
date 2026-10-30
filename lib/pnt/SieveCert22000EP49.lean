/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 480–489 of 1136

File 49 of 114: the parts `rows22000E_480` … `rows22000E_489` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 279 s of the kernel: row 109 columns 97–100, row 109 columns
101–271, row 110 columns 0–39, row 110 columns 40–57, row 110 columns 58–68, row 110 columns 69–77, row 110 columns
78–85, row 110 columns 86–91, row 110 columns 92–96, row 110 columns 97–101), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_480 : rowsJD 109 110 97 101 ≤ 136169382402830 := by decide +kernel

theorem rows22000E_481 : rowsJD 109 110 101 272 ≤ 192722949808762 := by decide +kernel

theorem rows22000E_482 : rowsJD 110 111 0 40 ≤ 152444708944539 := by decide +kernel

theorem rows22000E_483 : rowsJD 110 111 40 58 ≤ 160647350621826 := by decide +kernel

theorem rows22000E_484 : rowsJD 110 111 58 69 ≤ 107592976681548 := by decide +kernel

theorem rows22000E_485 : rowsJD 110 111 69 78 ≤ 46726521275231 := by decide +kernel

theorem rows22000E_486 : rowsJD 110 111 78 86 ≤ 51834771440764 := by decide +kernel

theorem rows22000E_487 : rowsJD 110 111 86 92 ≤ 56274333218280 := by decide +kernel

theorem rows22000E_488 : rowsJD 110 111 92 97 ≤ 98055906134473 := by decide +kernel

theorem rows22000E_489 : rowsJD 110 111 97 102 ≤ 170628861336283 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_480
#print axioms SieveDeep.rows22000E_489
