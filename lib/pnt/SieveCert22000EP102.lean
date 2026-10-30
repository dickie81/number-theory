/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1010–1019 of 1136

File 102 of 114: the parts `rows22000E_1010` … `rows22000E_1019` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 259 s of the kernel: row 189 columns 0–69, row 189 columns 70–79,
row 189 columns 80–271, row 190 columns 0–69, row 190 columns 70–98, row 190 columns 99–271, row 191 columns 0–68,
row 191 columns 69–98, row 191 columns 99–271, row 192 columns 0–68), each a sum of the costs (`rowsJD`) at most its
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

theorem rows22000E_1010 : rowsJD 189 190 0 70 ≤ 362285395342734 := by decide +kernel

theorem rows22000E_1011 : rowsJD 189 190 70 80 ≤ 464331203535240 := by decide +kernel

theorem rows22000E_1012 : rowsJD 189 190 80 272 ≤ 6745784275487156 := by decide +kernel

theorem rows22000E_1013 : rowsJD 190 191 0 70 ≤ 396815629064815 := by decide +kernel

theorem rows22000E_1014 : rowsJD 190 191 70 99 ≤ 622276597243680 := by decide +kernel

theorem rows22000E_1015 : rowsJD 190 191 99 272 ≤ 6597716982960638 := by decide +kernel

theorem rows22000E_1016 : rowsJD 191 192 0 69 ≤ 386929356197059 := by decide +kernel

theorem rows22000E_1017 : rowsJD 191 192 69 99 ≤ 767971923232388 := by decide +kernel

theorem rows22000E_1018 : rowsJD 191 192 99 272 ≤ 6592072945664392 := by decide +kernel

theorem rows22000E_1019 : rowsJD 192 193 0 69 ≤ 419836362394751 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1010
#print axioms SieveDeep.rows22000E_1019
