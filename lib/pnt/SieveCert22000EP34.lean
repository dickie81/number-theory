/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 330–339 of 1136

File 34 of 114: the parts `rows22000E_330` … `rows22000E_339` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 271 s of the kernel: row 95 columns 60–70, row 95 columns 71–78,
row 95 columns 79–84, row 95 columns 85–89, row 95 columns 90–92, row 95 columns 93–271, row 96 columns 0–37, row 96
columns 38–48, row 96 columns 49–60, row 96 columns 61–71), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_330 : rowsJD 95 96 60 71 ≤ 97506168801244 := by decide +kernel

theorem rows22000E_331 : rowsJD 95 96 71 79 ≤ 44732357020007 := by decide +kernel

theorem rows22000E_332 : rowsJD 95 96 79 85 ≤ 19102170942250 := by decide +kernel

theorem rows22000E_333 : rowsJD 95 96 85 90 ≤ 52961210966477 := by decide +kernel

theorem rows22000E_334 : rowsJD 95 96 90 93 ≤ 72978864570870 := by decide +kernel

theorem rows22000E_335 : rowsJD 95 96 93 272 ≤ 107298232410344 := by decide +kernel

theorem rows22000E_336 : rowsJD 96 97 0 38 ≤ 155373031087750 := by decide +kernel

theorem rows22000E_337 : rowsJD 96 97 38 49 ≤ 126219314250894 := by decide +kernel

theorem rows22000E_338 : rowsJD 96 97 49 61 ≤ 135661120023577 := by decide +kernel

theorem rows22000E_339 : rowsJD 96 97 61 72 ≤ 89189338134097 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_330
#print axioms SieveDeep.rows22000E_339
