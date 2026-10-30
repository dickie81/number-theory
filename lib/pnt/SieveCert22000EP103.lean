/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1020–1029 of 1136

File 103 of 114: the parts `rows22000E_1020` … `rows22000E_1029` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 248 s of the kernel: row 192 columns 69–101, row 192 columns
102–271, row 193 columns 0–67, row 193 columns 68–101, row 193 columns 102–271, row 194 columns 0–66, row 194
columns 67–101, row 194 columns 102–271, row 195 columns 0–65, row 195 columns 66–100), each a sum of the costs
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

theorem rows22000E_1020 : rowsJD 192 193 69 102 ≤ 1199196092487170 := by decide +kernel

theorem rows22000E_1021 : rowsJD 192 193 102 272 ≤ 6157948799689893 := by decide +kernel

theorem rows22000E_1022 : rowsJD 193 194 0 68 ≤ 412474287796858 := by decide +kernel

theorem rows22000E_1023 : rowsJD 193 194 68 102 ≤ 1321180960886978 := by decide +kernel

theorem rows22000E_1024 : rowsJD 193 194 102 272 ≤ 6156183357147945 := by decide +kernel

theorem rows22000E_1025 : rowsJD 194 195 0 67 ≤ 404486193440200 := by decide +kernel

theorem rows22000E_1026 : rowsJD 194 195 67 102 ≤ 1446687036009821 := by decide +kernel

theorem rows22000E_1027 : rowsJD 194 195 102 272 ≤ 6063645688918236 := by decide +kernel

theorem rows22000E_1028 : rowsJD 195 196 0 66 ≤ 395052762981691 := by decide +kernel

theorem rows22000E_1029 : rowsJD 195 196 66 101 ≤ 1466455472878848 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1020
#print axioms SieveDeep.rows22000E_1029
