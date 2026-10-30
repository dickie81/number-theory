/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1050–1059 of 1136

File 106 of 114: the parts `rows22000E_1050` … `rows22000E_1059` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 226 s of the kernel: row 202 columns 61–108, row 202 columns
109–271, row 203 columns 0–60, row 203 columns 61–113, row 203 columns 114–271, row 204 columns 0–59, row 204
columns 60–113, row 204 columns 114–271, row 205 columns 0–59, row 205 columns 60–131), each a sum of the costs
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

theorem rows22000E_1050 : rowsJD 202 203 61 109 ≤ 3140953737535736 := by decide +kernel

theorem rows22000E_1051 : rowsJD 202 203 109 272 ≤ 4980594603920140 := by decide +kernel

theorem rows22000E_1052 : rowsJD 203 204 0 61 ≤ 547988259303741 := by decide +kernel

theorem rows22000E_1053 : rowsJD 203 204 61 114 ≤ 3714629463604857 := by decide +kernel

theorem rows22000E_1054 : rowsJD 203 204 114 272 ≤ 4479186140625238 := by decide +kernel

theorem rows22000E_1055 : rowsJD 204 205 0 60 ≤ 510361484150202 := by decide +kernel

theorem rows22000E_1056 : rowsJD 204 205 60 114 ≤ 3839285412926968 := by decide +kernel

theorem rows22000E_1057 : rowsJD 204 205 114 272 ≤ 4388895472286694 := by decide +kernel

theorem rows22000E_1058 : rowsJD 205 206 0 60 ≤ 566008804125010 := by decide +kernel

theorem rows22000E_1059 : rowsJD 205 206 60 132 ≤ 5681630203529676 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1050
#print axioms SieveDeep.rows22000E_1059
