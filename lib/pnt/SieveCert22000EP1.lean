/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 0–9 of 1136

File 1 of 114: the parts `rows22000E_0` … `rows22000E_9` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 216 s of the kernel: rows 0–16, rows 17–20, rows 21–23, rows
24–25, rows 26–27, rows 28–28, rows 29–29, rows 30–30, rows 31–31, rows 32–32), each a sum of the costs (`rowsJD`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_0 : rowsJD 0 17 0 272 ≤ 273050983399026 := by decide +kernel

theorem rows22000E_1 : rowsJD 17 21 0 272 ≤ 310215333210655 := by decide +kernel

theorem rows22000E_2 : rowsJD 21 24 0 272 ≤ 359474705587671 := by decide +kernel

theorem rows22000E_3 : rowsJD 24 26 0 272 ≤ 313618335425120 := by decide +kernel

theorem rows22000E_4 : rowsJD 26 28 0 272 ≤ 381512216634183 := by decide +kernel

theorem rows22000E_5 : rowsJD 28 29 0 272 ≤ 218632493714871 := by decide +kernel

theorem rows22000E_6 : rowsJD 29 30 0 272 ≤ 238657200603596 := by decide +kernel

theorem rows22000E_7 : rowsJD 30 31 0 272 ≤ 259915524392846 := by decide +kernel

theorem rows22000E_8 : rowsJD 31 32 0 272 ≤ 282502148496733 := by decide +kernel

theorem rows22000E_9 : rowsJD 32 33 0 272 ≤ 305474883568568 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_0
#print axioms SieveDeep.rows22000E_9
