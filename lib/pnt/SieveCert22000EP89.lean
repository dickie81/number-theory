/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 880–889 of 1136

File 89 of 114: the parts `rows22000E_880` … `rows22000E_889` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 268 s of the kernel: row 163 columns 0–43, row 163 columns 44–76,
row 163 columns 77–88, row 163 columns 89–96, row 163 columns 97–101, row 163 columns 102–105, row 163 columns
106–271, row 164 columns 0–43, row 164 columns 44–77, row 164 columns 78–89), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_880 : rowsJD 163 164 0 44 ≤ 23668521134022 := by decide +kernel

theorem rows22000E_881 : rowsJD 163 164 44 77 ≤ 234130538927960 := by decide +kernel

theorem rows22000E_882 : rowsJD 163 164 77 89 ≤ 567360389387880 := by decide +kernel

theorem rows22000E_883 : rowsJD 163 164 89 97 ≤ 374991439337444 := by decide +kernel

theorem rows22000E_884 : rowsJD 163 164 97 102 ≤ 391033708674600 := by decide +kernel

theorem rows22000E_885 : rowsJD 163 164 102 106 ≤ 452991976260603 := by decide +kernel

theorem rows22000E_886 : rowsJD 163 164 106 272 ≤ 3837430379190635 := by decide +kernel

theorem rows22000E_887 : rowsJD 164 165 0 44 ≤ 24127309049568 := by decide +kernel

theorem rows22000E_888 : rowsJD 164 165 44 78 ≤ 329644097400816 := by decide +kernel

theorem rows22000E_889 : rowsJD 164 165 78 90 ≤ 582618737088507 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_880
#print axioms SieveDeep.rows22000E_889
