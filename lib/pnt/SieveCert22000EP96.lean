/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 950–959 of 1136

File 96 of 114: the parts `rows22000E_950` … `rows22000E_959` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 266 s of the kernel: row 175 columns 80–87, row 175 columns
88–112, row 175 columns 113–271, row 176 columns 0–64, row 176 columns 65–79, row 176 columns 80–87, row 176 columns
88–112, row 176 columns 113–271, row 177 columns 0–65, row 177 columns 66–79), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_950 : rowsJD 175 176 80 88 ≤ 601453195150174 := by decide +kernel

theorem rows22000E_951 : rowsJD 175 176 88 113 ≤ 732279212237283 := by decide +kernel

theorem rows22000E_952 : rowsJD 175 176 113 272 ≤ 5882641498685386 := by decide +kernel

theorem rows22000E_953 : rowsJD 176 177 0 65 ≤ 172596263414699 := by decide +kernel

theorem rows22000E_954 : rowsJD 176 177 65 80 ≤ 568893009134483 := by decide +kernel

theorem rows22000E_955 : rowsJD 176 177 80 88 ≤ 607476344679264 := by decide +kernel

theorem rows22000E_956 : rowsJD 176 177 88 113 ≤ 719219219423418 := by decide +kernel

theorem rows22000E_957 : rowsJD 176 177 113 272 ≤ 5788106517151563 := by decide +kernel

theorem rows22000E_958 : rowsJD 177 178 0 66 ≤ 175099035624177 := by decide +kernel

theorem rows22000E_959 : rowsJD 177 178 66 80 ≤ 500412714803006 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_950
#print axioms SieveDeep.rows22000E_959
