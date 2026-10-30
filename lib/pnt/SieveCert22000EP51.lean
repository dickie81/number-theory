/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 500–509 of 1136

File 51 of 114: the parts `rows22000E_500` … `rows22000E_509` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 275 s of the kernel: row 112 columns 0–39, row 112 columns 40–59,
row 112 columns 60–69, row 112 columns 70–79, row 112 columns 80–86, row 112 columns 87–92, row 112 columns 93–98,
row 112 columns 99–271, row 113 columns 0–39, row 113 columns 40–59), each a sum of the costs (`rowsJD`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_500 : rowsJD 112 113 0 40 ≤ 153818771687416 := by decide +kernel

theorem rows22000E_501 : rowsJD 112 113 40 60 ≤ 168608510065476 := by decide +kernel

theorem rows22000E_502 : rowsJD 112 113 60 70 ≤ 129034728073022 := by decide +kernel

theorem rows22000E_503 : rowsJD 112 113 70 80 ≤ 59589623040649 := by decide +kernel

theorem rows22000E_504 : rowsJD 112 113 80 87 ≤ 72723776814291 := by decide +kernel

theorem rows22000E_505 : rowsJD 112 113 87 93 ≤ 75531219359359 := by decide +kernel

theorem rows22000E_506 : rowsJD 112 113 93 99 ≤ 137108241412208 := by decide +kernel

theorem rows22000E_507 : rowsJD 112 113 99 272 ≤ 101290666447649 := by decide +kernel

theorem rows22000E_508 : rowsJD 113 114 0 40 ≤ 151529289868595 := by decide +kernel

theorem rows22000E_509 : rowsJD 113 114 40 60 ≤ 158954688013747 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_500
#print axioms SieveDeep.rows22000E_509
