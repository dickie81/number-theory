/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1110–1119 of 1136

File 112 of 114: the parts `rows22000E_1110` … `rows22000E_1119` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 273 s of the kernel: row 230 columns 0–66, row 230 columns 67–271,
row 231 columns 0–62, row 231 columns 63–271, row 232 columns 0–59, row 232 columns 60–271, row 233 columns 0–59,
row 233 columns 60–271, rows 234–254, rows 255–255), each a sum of the costs (`rowsJD`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_1110 : rowsJD 230 231 0 67 ≤ 1858311785459729 := by decide +kernel

theorem rows22000E_1111 : rowsJD 230 231 67 272 ≤ 9309439016648847 := by decide +kernel

theorem rows22000E_1112 : rowsJD 231 232 0 63 ≤ 1063292114261312 := by decide +kernel

theorem rows22000E_1113 : rowsJD 231 232 63 272 ≤ 10127171003807077 := by decide +kernel

theorem rows22000E_1114 : rowsJD 232 233 0 60 ≤ 556254985402150 := by decide +kernel

theorem rows22000E_1115 : rowsJD 232 233 60 272 ≤ 10569181116039968 := by decide +kernel

theorem rows22000E_1116 : rowsJD 233 234 0 60 ≤ 582349628651434 := by decide +kernel

theorem rows22000E_1117 : rowsJD 233 234 60 272 ≤ 10551778793867791 := by decide +kernel

theorem rows22000E_1118 : rowsJD 234 255 0 272 ≤ 13467240788558229 := by decide +kernel

theorem rows22000E_1119 : rowsJD 255 256 0 272 ≤ 13522873843755431 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1110
#print axioms SieveDeep.rows22000E_1119
