/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1040–1049 of 1136

File 105 of 114: the parts `rows22000E_1040` … `rows22000E_1049` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 235 s of the kernel: row 199 columns 0–62, row 199 columns 63–103,
row 199 columns 104–271, row 200 columns 0–61, row 200 columns 62–103, row 200 columns 104–271, row 201 columns
0–61, row 201 columns 62–108, row 201 columns 109–271, row 202 columns 0–60), each a sum of the costs (`rowsJD`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_1040 : rowsJD 199 200 0 63 ≤ 473075753051018 := by decide +kernel

theorem rows22000E_1041 : rowsJD 199 200 63 104 ≤ 2294518581154740 := by decide +kernel

theorem rows22000E_1042 : rowsJD 199 200 104 272 ≤ 5672613989711556 := by decide +kernel

theorem rows22000E_1043 : rowsJD 200 201 0 62 ≤ 486604593925343 := by decide +kernel

theorem rows22000E_1044 : rowsJD 200 201 62 104 ≤ 2431666868516252 := by decide +kernel

theorem rows22000E_1045 : rowsJD 200 201 104 272 ≤ 5581822276690034 := by decide +kernel

theorem rows22000E_1046 : rowsJD 201 202 0 62 ≤ 552268899692663 := by decide +kernel

theorem rows22000E_1047 : rowsJD 201 202 62 109 ≤ 3028582606768471 := by decide +kernel

theorem rows22000E_1048 : rowsJD 201 202 109 272 ≤ 5071058071525963 := by decide +kernel

theorem rows22000E_1049 : rowsJD 202 203 0 61 ≤ 524069427032889 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1040
#print axioms SieveDeep.rows22000E_1049
