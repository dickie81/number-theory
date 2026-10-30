/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1030–1039 of 1136

File 104 of 114: the parts `rows22000E_1030` … `rows22000E_1039` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 228 s of the kernel: row 195 columns 101–271, row 196 columns
0–64, row 196 columns 65–99, row 196 columns 100–271, row 197 columns 0–64, row 197 columns 65–103, row 197 columns
104–271, row 198 columns 0–63, row 198 columns 64–103, row 198 columns 104–271), each a sum of the costs (`rowsJD`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_1030 : rowsJD 195 196 101 272 ≤ 6169404000453160 := by decide +kernel

theorem rows22000E_1031 : rowsJD 196 197 0 65 ≤ 386258940473211 := by decide +kernel

theorem rows22000E_1032 : rowsJD 196 197 65 100 ≤ 1484800475172759 := by decide +kernel

theorem rows22000E_1033 : rowsJD 196 197 100 272 ≤ 6186241078399890 := by decide +kernel

theorem rows22000E_1034 : rowsJD 197 198 0 65 ≤ 458879764089159 := by decide +kernel

theorem rows22000E_1035 : rowsJD 197 198 65 104 ≤ 2014652173459948 := by decide +kernel

theorem rows22000E_1036 : rowsJD 197 198 104 272 ≤ 5763183713970880 := by decide +kernel

theorem rows22000E_1037 : rowsJD 198 199 0 64 ≤ 460336230127744 := by decide +kernel

theorem rows22000E_1038 : rowsJD 198 199 64 104 ≤ 2155204578758805 := by decide +kernel

theorem rows22000E_1039 : rowsJD 198 199 104 272 ≤ 5672153193010136 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1030
#print axioms SieveDeep.rows22000E_1039
