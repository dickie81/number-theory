/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 710–719 of 1136

File 72 of 114: the parts `rows22000E_710` … `rows22000E_719` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 261 s of the kernel: row 140 columns 73–99, row 140 columns
100–108, row 140 columns 109–126, row 140 columns 127–271, row 141 columns 0–47, row 141 columns 48–60, row 141
columns 61–71, row 141 columns 72–98, row 141 columns 99–107, row 141 columns 108–120), each a sum of the costs
(`rowsJD`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_710 : rowsJD 140 141 73 100 ≤ 253198081293627 := by decide +kernel

theorem rows22000E_711 : rowsJD 140 141 100 109 ≤ 341397117683925 := by decide +kernel

theorem rows22000E_712 : rowsJD 140 141 109 127 ≤ 1406868394219919 := by decide +kernel

theorem rows22000E_713 : rowsJD 140 141 127 272 ≤ 309229757849770 := by decide +kernel

theorem rows22000E_714 : rowsJD 141 142 0 48 ≤ 74055231751022 := by decide +kernel

theorem rows22000E_715 : rowsJD 141 142 48 61 ≤ 27075118941538 := by decide +kernel

theorem rows22000E_716 : rowsJD 141 142 61 72 ≤ 193370095142935 := by decide +kernel

theorem rows22000E_717 : rowsJD 141 142 72 99 ≤ 289500312264562 := by decide +kernel

theorem rows22000E_718 : rowsJD 141 142 99 108 ≤ 353446662691286 := by decide +kernel

theorem rows22000E_719 : rowsJD 141 142 108 121 ≤ 838753197016533 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_710
#print axioms SieveDeep.rows22000E_719
