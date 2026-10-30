/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 60–69 of 1136

File 7 of 114: the parts `rows22000E_60` … `rows22000E_69` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 233 s of the kernel: row 55 columns 47–54, row 55 columns 55–271,
row 56 columns 0–36, row 56 columns 37–47, row 56 columns 48–54, row 56 columns 55–271, row 57 columns 0–36, row 57
columns 37–47, row 57 columns 48–54, row 57 columns 55–271), each a sum of the costs (`rowsJD`) at most its bound,
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

theorem rows22000E_60 : rowsJD 55 56 47 55 ≤ 214975799716221 := by decide +kernel

theorem rows22000E_61 : rowsJD 55 56 55 272 ≤ 23618462985292 := by decide +kernel

theorem rows22000E_62 : rowsJD 56 57 0 37 ≤ 290327578923013 := by decide +kernel

theorem rows22000E_63 : rowsJD 56 57 37 48 ≤ 305880002654789 := by decide +kernel

theorem rows22000E_64 : rowsJD 56 57 48 55 ≤ 177216497873800 := by decide +kernel

theorem rows22000E_65 : rowsJD 56 57 55 272 ≤ 44478076400719 := by decide +kernel

theorem rows22000E_66 : rowsJD 57 58 0 37 ≤ 286781864026203 := by decide +kernel

theorem rows22000E_67 : rowsJD 57 58 37 48 ≤ 297655421463576 := by decide +kernel

theorem rows22000E_68 : rowsJD 57 58 48 55 ≤ 168596937311513 := by decide +kernel

theorem rows22000E_69 : rowsJD 57 58 55 272 ≤ 62518942573653 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_60
#print axioms SieveDeep.rows22000E_69
