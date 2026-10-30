/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 490–499 of 1136

File 50 of 114: the parts `rows22000E_490` … `rows22000E_499` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 241 s of the kernel: row 110 columns 102–271, row 111 columns
0–39, row 111 columns 40–58, row 111 columns 59–69, row 111 columns 70–79, row 111 columns 80–86, row 111 columns
87–92, row 111 columns 93–97, row 111 columns 98–101, row 111 columns 102–271), each a sum of the costs (`rowsJD`)
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

theorem rows22000E_490 : rowsJD 110 111 102 272 ≤ 92387717663460 := by decide +kernel

theorem rows22000E_491 : rowsJD 111 112 0 40 ≤ 154311819879246 := by decide +kernel

theorem rows22000E_492 : rowsJD 111 112 40 59 ≤ 164412755656350 := by decide +kernel

theorem rows22000E_493 : rowsJD 111 112 59 70 ≤ 122857144430179 := by decide +kernel

theorem rows22000E_494 : rowsJD 111 112 70 80 ≤ 50177865676232 := by decide +kernel

theorem rows22000E_495 : rowsJD 111 112 80 87 ≤ 62348073238567 := by decide +kernel

theorem rows22000E_496 : rowsJD 111 112 87 93 ≤ 67500476103690 := by decide +kernel

theorem rows22000E_497 : rowsJD 111 112 93 98 ≤ 107967193346365 := by decide +kernel

theorem rows22000E_498 : rowsJD 111 112 98 102 ≤ 137292195559143 := by decide +kernel

theorem rows22000E_499 : rowsJD 111 112 102 272 ≤ 42599465396495 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_490
#print axioms SieveDeep.rows22000E_499
