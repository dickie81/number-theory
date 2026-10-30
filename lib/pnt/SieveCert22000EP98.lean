/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 970–979 of 1136

File 98 of 114: the parts `rows22000E_970` … `rows22000E_979` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 256 s of the kernel: row 179 columns 81–87, row 179 columns
88–112, row 179 columns 113–271, row 180 columns 0–68, row 180 columns 69–80, row 180 columns 81–87, row 180 columns
88–113, row 180 columns 114–271, row 181 columns 0–68, row 181 columns 69–80), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_970 : rowsJD 179 180 81 88 ≤ 519309810729437 := by decide +kernel

theorem rows22000E_971 : rowsJD 179 180 88 113 ≤ 592078657532050 := by decide +kernel

theorem rows22000E_972 : rowsJD 179 180 113 272 ≤ 5674253000319378 := by decide +kernel

theorem rows22000E_973 : rowsJD 180 181 0 69 ≤ 161036975683229 := by decide +kernel

theorem rows22000E_974 : rowsJD 180 181 69 81 ≤ 408456879879089 := by decide +kernel

theorem rows22000E_975 : rowsJD 180 181 81 88 ≤ 491438281033229 := by decide +kernel

theorem rows22000E_976 : rowsJD 180 181 88 114 ≤ 666942001485238 := by decide +kernel

theorem rows22000E_977 : rowsJD 180 181 114 272 ≤ 5483884631919540 := by decide +kernel

theorem rows22000E_978 : rowsJD 181 182 0 69 ≤ 151717961688138 := by decide +kernel

theorem rows22000E_979 : rowsJD 181 182 69 81 ≤ 391702900689730 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_970
#print axioms SieveDeep.rows22000E_979
