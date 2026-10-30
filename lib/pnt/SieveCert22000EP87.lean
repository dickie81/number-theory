/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 860–869 of 1136

File 87 of 114: the parts `rows22000E_860` … `rows22000E_869` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 279 s of the kernel: row 160 columns 45–77, row 160 columns 78–89,
row 160 columns 90–97, row 160 columns 98–102, row 160 columns 103–106, row 160 columns 107–271, row 161 columns
0–43, row 161 columns 44–75, row 161 columns 76–88, row 161 columns 89–96), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_860 : rowsJD 160 161 45 78 ≤ 156078608904443 := by decide +kernel

theorem rows22000E_861 : rowsJD 160 161 78 90 ≤ 528720698653127 := by decide +kernel

theorem rows22000E_862 : rowsJD 160 161 90 98 ≤ 417636234037569 := by decide +kernel

theorem rows22000E_863 : rowsJD 160 161 98 103 ≤ 447381878004662 := by decide +kernel

theorem rows22000E_864 : rowsJD 160 161 103 107 ≤ 494855745730234 := by decide +kernel

theorem rows22000E_865 : rowsJD 160 161 107 272 ≤ 3495910110044709 := by decide +kernel

theorem rows22000E_866 : rowsJD 161 162 0 44 ≤ 23438291009556 := by decide +kernel

theorem rows22000E_867 : rowsJD 161 162 44 76 ≤ 125565129739032 := by decide +kernel

theorem rows22000E_868 : rowsJD 161 162 76 89 ≤ 565779951302700 := by decide +kernel

theorem rows22000E_869 : rowsJD 161 162 89 97 ≤ 381864313492021 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_860
#print axioms SieveDeep.rows22000E_869
