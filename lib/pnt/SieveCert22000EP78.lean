/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 770–779 of 1136

File 78 of 114: the parts `rows22000E_770` … `rows22000E_779` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 238 s of the kernel: row 148 columns 120–271, row 149 columns
0–46, row 149 columns 47–57, row 149 columns 58–87, row 149 columns 88–95, row 149 columns 96–102, row 149 columns
103–108, row 149 columns 109–114, row 149 columns 115–271, row 150 columns 0–46), each a sum of the costs (`rowsJD`)
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

theorem rows22000E_770 : rowsJD 148 149 120 272 ≤ 1081756206235605 := by decide +kernel

theorem rows22000E_771 : rowsJD 149 150 0 47 ≤ 48165713658769 := by decide +kernel

theorem rows22000E_772 : rowsJD 149 150 47 58 ≤ 15749850414801 := by decide +kernel

theorem rows22000E_773 : rowsJD 149 150 58 88 ≤ 271480098199903 := by decide +kernel

theorem rows22000E_774 : rowsJD 149 150 88 96 ≤ 487594566576722 := by decide +kernel

theorem rows22000E_775 : rowsJD 149 150 96 103 ≤ 447920850339945 := by decide +kernel

theorem rows22000E_776 : rowsJD 149 150 103 109 ≤ 398711787109802 := by decide +kernel

theorem rows22000E_777 : rowsJD 149 150 109 115 ≤ 394267205388543 := by decide +kernel

theorem rows22000E_778 : rowsJD 149 150 115 272 ≤ 1668762118708070 := by decide +kernel

theorem rows22000E_779 : rowsJD 150 151 0 47 ≤ 45157171418562 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_770
#print axioms SieveDeep.rows22000E_779
