/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 540–549 of 1136

File 55 of 114: the parts `rows22000E_540` … `rows22000E_549` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 260 s of the kernel: row 117 columns 61–69, row 117 columns 70–79,
row 117 columns 80–86, row 117 columns 87–91, row 117 columns 92–114, row 117 columns 115–271, row 118 columns 0–40,
row 118 columns 41–61, row 118 columns 62–70, row 118 columns 71–80), each a sum of the costs (`rowsJD`) at most its
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

theorem rows22000E_540 : rowsJD 117 118 61 70 ≤ 143869301159667 := by decide +kernel

theorem rows22000E_541 : rowsJD 117 118 70 80 ≤ 95615312368412 := by decide +kernel

theorem rows22000E_542 : rowsJD 117 118 80 87 ≤ 143240856918051 := by decide +kernel

theorem rows22000E_543 : rowsJD 117 118 87 92 ≤ 118617232610033 := by decide +kernel

theorem rows22000E_544 : rowsJD 117 118 92 115 ≤ 123448551197152 := by decide +kernel

theorem rows22000E_545 : rowsJD 117 118 115 272 ≤ 399205287418167 := by decide +kernel

theorem rows22000E_546 : rowsJD 118 119 0 41 ≤ 147763939947544 := by decide +kernel

theorem rows22000E_547 : rowsJD 118 119 41 62 ≤ 158464537111511 := by decide +kernel

theorem rows22000E_548 : rowsJD 118 119 62 71 ≤ 147502183232953 := by decide +kernel

theorem rows22000E_549 : rowsJD 118 119 71 81 ≤ 116119118522359 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_540
#print axioms SieveDeep.rows22000E_549
