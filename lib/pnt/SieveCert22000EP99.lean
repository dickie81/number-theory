/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 980–989 of 1136

File 99 of 114: the parts `rows22000E_980` … `rows22000E_989` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 243 s of the kernel: row 181 columns 81–87, row 181 columns
88–115, row 181 columns 116–271, row 182 columns 0–69, row 182 columns 70–80, row 182 columns 81–107, row 182
columns 108–142, row 182 columns 143–271, row 183 columns 0–69, row 183 columns 70–80), each a sum of the costs
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

theorem rows22000E_980 : rowsJD 181 182 81 88 ≤ 479692925720402 := by decide +kernel

theorem rows22000E_981 : rowsJD 181 182 88 116 ≤ 868453101002184 := by decide +kernel

theorem rows22000E_982 : rowsJD 181 182 116 272 ≤ 5288501164377148 := by decide +kernel

theorem rows22000E_983 : rowsJD 182 183 0 70 ≤ 168771573989546 := by decide +kernel

theorem rows22000E_984 : rowsJD 182 183 70 81 ≤ 363929195736295 := by decide +kernel

theorem rows22000E_985 : rowsJD 182 183 81 108 ≤ 682253042731062 := by decide +kernel

theorem rows22000E_986 : rowsJD 182 183 108 143 ≤ 3314999336944815 := by decide +kernel

theorem rows22000E_987 : rowsJD 182 183 143 272 ≤ 2589677396173391 := by decide +kernel

theorem rows22000E_988 : rowsJD 183 184 0 70 ≤ 178529080846866 := by decide +kernel

theorem rows22000E_989 : rowsJD 183 184 70 81 ≤ 361253181334795 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_980
#print axioms SieveDeep.rows22000E_989
