/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 340–349 of 1136

File 35 of 114: the parts `rows22000E_340` … `rows22000E_349` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 255 s of the kernel: row 96 columns 72–79, row 96 columns 80–85,
row 96 columns 86–89, row 96 columns 90–92, row 96 columns 93–95, row 96 columns 96–271, row 97 columns 0–38, row 97
columns 39–49, row 97 columns 50–62, row 97 columns 63–73), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_340 : rowsJD 96 97 72 80 ≤ 43946647724306 := by decide +kernel

theorem rows22000E_341 : rowsJD 96 97 80 86 ≤ 18165838204774 := by decide +kernel

theorem rows22000E_342 : rowsJD 96 97 86 90 ≤ 46215764341468 := by decide +kernel

theorem rows22000E_343 : rowsJD 96 97 90 93 ≤ 71305707781261 := by decide +kernel

theorem rows22000E_344 : rowsJD 96 97 93 96 ≤ 104078217060012 := by decide +kernel

theorem rows22000E_345 : rowsJD 96 97 96 272 ≤ 43986496769578 := by decide +kernel

theorem rows22000E_346 : rowsJD 97 98 0 39 ≤ 158035122640617 := by decide +kernel

theorem rows22000E_347 : rowsJD 97 98 39 50 ≤ 135065518490470 := by decide +kernel

theorem rows22000E_348 : rowsJD 97 98 50 63 ≤ 132663097915678 := by decide +kernel

theorem rows22000E_349 : rowsJD 97 98 63 74 ≤ 80967166384091 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_340
#print axioms SieveDeep.rows22000E_349
