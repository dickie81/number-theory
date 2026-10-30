/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 520–529 of 1136

File 53 of 114: the parts `rows22000E_520` … `rows22000E_529` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 261 s of the kernel: row 114 columns 80–86, row 114 columns 87–92,
row 114 columns 93–98, row 114 columns 99–271, row 115 columns 0–39, row 115 columns 40–59, row 115 columns 60–69,
row 115 columns 70–79, row 115 columns 80–86, row 115 columns 87–92), each a sum of the costs (`rowsJD`) at most its
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

theorem rows22000E_520 : rowsJD 114 115 80 87 ≤ 97371312056366 := by decide +kernel

theorem rows22000E_521 : rowsJD 114 115 87 93 ≤ 100529556684617 := by decide +kernel

theorem rows22000E_522 : rowsJD 114 115 93 99 ≤ 138774655306534 := by decide +kernel

theorem rows22000E_523 : rowsJD 114 115 99 272 ≤ 29756138420788 := by decide +kernel

theorem rows22000E_524 : rowsJD 115 116 0 40 ≤ 145167038888791 := by decide +kernel

theorem rows22000E_525 : rowsJD 115 116 40 60 ≤ 140125678766193 := by decide +kernel

theorem rows22000E_526 : rowsJD 115 116 60 70 ≤ 144107109106653 := by decide +kernel

theorem rows22000E_527 : rowsJD 115 116 70 80 ≤ 82050142712783 := by decide +kernel

theorem rows22000E_528 : rowsJD 115 116 80 87 ≤ 111895675516306 := by decide +kernel

theorem rows22000E_529 : rowsJD 115 116 87 93 ≤ 115595515032578 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_520
#print axioms SieveDeep.rows22000E_529
