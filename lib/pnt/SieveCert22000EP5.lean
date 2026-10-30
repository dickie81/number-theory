/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 40–49 of 1136

File 5 of 114: the parts `rows22000E_40` … `rows22000E_49` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 242 s of the kernel: row 49 columns 0–36, row 49 columns 37–46,
row 49 columns 47–271, row 50 columns 0–36, row 50 columns 37–46, row 50 columns 47–271, row 51 columns 0–36, row 51
columns 37–46, row 51 columns 47–271, row 52 columns 0–36), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_40 : rowsJD 49 50 0 37 ≤ 315603119208180 := by decide +kernel

theorem rows22000E_41 : rowsJD 49 50 37 47 ≤ 321249941249269 := by decide +kernel

theorem rows22000E_42 : rowsJD 49 50 47 272 ≤ 106380618226877 := by decide +kernel

theorem rows22000E_43 : rowsJD 50 51 0 37 ≤ 311218211560638 := by decide +kernel

theorem rows22000E_44 : rowsJD 50 51 37 47 ≤ 316424292325331 := by decide +kernel

theorem rows22000E_45 : rowsJD 50 51 47 272 ≤ 136351211712048 := by decide +kernel

theorem rows22000E_46 : rowsJD 51 52 0 37 ≤ 307391376509008 := by decide +kernel

theorem rows22000E_47 : rowsJD 51 52 37 47 ≤ 310888605688757 := by decide +kernel

theorem rows22000E_48 : rowsJD 51 52 47 272 ≤ 163358416885680 := by decide +kernel

theorem rows22000E_49 : rowsJD 52 53 0 37 ≤ 304024972411132 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_40
#print axioms SieveDeep.rows22000E_49
