/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 530–539 of 1136

File 54 of 114: the parts `rows22000E_530` … `rows22000E_539` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 286 s of the kernel: row 115 columns 93–271, row 116 columns 0–39,
row 116 columns 40–60, row 116 columns 61–69, row 116 columns 70–79, row 116 columns 80–86, row 116 columns 87–92,
row 116 columns 93–271, row 117 columns 0–39, row 117 columns 40–60), each a sum of the costs (`rowsJD`) at most its
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

theorem rows22000E_530 : rowsJD 115 116 93 272 ≤ 141449077623986 := by decide +kernel

theorem rows22000E_531 : rowsJD 116 117 0 40 ≤ 141052338411971 := by decide +kernel

theorem rows22000E_532 : rowsJD 116 117 40 61 ≤ 141599564017279 := by decide +kernel

theorem rows22000E_533 : rowsJD 116 117 61 70 ≤ 133420850614803 := by decide +kernel

theorem rows22000E_534 : rowsJD 116 117 70 80 ≤ 83593738760107 := by decide +kernel

theorem rows22000E_535 : rowsJD 116 117 80 87 ≤ 126493555172407 := by decide +kernel

theorem rows22000E_536 : rowsJD 116 117 87 93 ≤ 130168586200455 := by decide +kernel

theorem rows22000E_537 : rowsJD 116 117 93 272 ≤ 262453580170177 := by decide +kernel

theorem rows22000E_538 : rowsJD 117 118 0 40 ≤ 140119422712564 := by decide +kernel

theorem rows22000E_539 : rowsJD 117 118 40 61 ≤ 146128006839412 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_530
#print axioms SieveDeep.rows22000E_539
