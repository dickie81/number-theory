/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 120–129 of 1136

File 13 of 114: the parts `rows22000E_120` … `rows22000E_129` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 272 s of the kernel: row 67 columns 48–54, row 67 columns 55–59,
row 67 columns 60–63, row 67 columns 64–271, row 68 columns 0–36, row 68 columns 37–47, row 68 columns 48–54, row 68
columns 55–59, row 68 columns 60–63, row 68 columns 64–271), each a sum of the costs (`rowsJD`) at most its bound,
by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_120 : rowsJD 67 68 48 55 ≤ 105793631975805 := by decide +kernel

theorem rows22000E_121 : rowsJD 67 68 55 60 ≤ 67594509967161 := by decide +kernel

theorem rows22000E_122 : rowsJD 67 68 60 64 ≤ 61066170811203 := by decide +kernel

theorem rows22000E_123 : rowsJD 67 68 64 272 ≤ 55025751622480 := by decide +kernel

theorem rows22000E_124 : rowsJD 68 69 0 37 ≤ 254099481776642 := by decide +kernel

theorem rows22000E_125 : rowsJD 68 69 37 48 ≤ 213599288753676 := by decide +kernel

theorem rows22000E_126 : rowsJD 68 69 48 55 ≤ 101816882768992 := by decide +kernel

theorem rows22000E_127 : rowsJD 68 69 55 60 ≤ 66118631996282 := by decide +kernel

theorem rows22000E_128 : rowsJD 68 69 60 64 ≤ 58705017874742 := by decide +kernel

theorem rows22000E_129 : rowsJD 68 69 64 272 ≤ 64363408656460 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_120
#print axioms SieveDeep.rows22000E_129
