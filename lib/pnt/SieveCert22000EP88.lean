/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 870–879 of 1136

File 88 of 114: the parts `rows22000E_870` … `rows22000E_879` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 266 s of the kernel: row 161 columns 97–101, row 161 columns
102–105, row 161 columns 106–271, row 162 columns 0–43, row 162 columns 44–76, row 162 columns 77–88, row 162
columns 89–96, row 162 columns 97–101, row 162 columns 102–105, row 162 columns 106–271), each a sum of the costs
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

theorem rows22000E_870 : rowsJD 161 162 97 102 ≤ 407609122986638 := by decide +kernel

theorem rows22000E_871 : rowsJD 161 162 102 106 ≤ 468530367384342 := by decide +kernel

theorem rows22000E_872 : rowsJD 161 162 106 272 ≤ 3702336347031499 := by decide +kernel

theorem rows22000E_873 : rowsJD 162 163 0 44 ≤ 23832283546313 := by decide +kernel

theorem rows22000E_874 : rowsJD 162 163 44 77 ≤ 195274778090763 := by decide +kernel

theorem rows22000E_875 : rowsJD 162 163 77 89 ≤ 546439723793362 := by decide +kernel

theorem rows22000E_876 : rowsJD 162 163 89 97 ≤ 379217481195459 := by decide +kernel

theorem rows22000E_877 : rowsJD 162 163 97 102 ≤ 401445509128827 := by decide +kernel

theorem rows22000E_878 : rowsJD 162 163 102 106 ≤ 461744904924832 := by decide +kernel

theorem rows22000E_879 : rowsJD 162 163 106 272 ≤ 3770356845486786 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_870
#print axioms SieveDeep.rows22000E_879
