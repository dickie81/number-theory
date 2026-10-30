/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1000–1009 of 1136

File 101 of 114: the parts `rows22000E_1000` … `rows22000E_1009` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 261 s of the kernel: row 186 columns 0–70, row 186 columns 71–80,
row 186 columns 81–131, row 186 columns 132–271, row 187 columns 0–70, row 187 columns 71–80, row 187 columns
81–271, row 188 columns 0–70, row 188 columns 71–80, row 188 columns 81–271), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_1000 : rowsJD 186 187 0 71 ≤ 292335314495738 := by decide +kernel

theorem rows22000E_1001 : rowsJD 186 187 71 81 ≤ 372509399093073 := by decide +kernel

theorem rows22000E_1002 : rowsJD 186 187 81 132 ≤ 3142263294588464 := by decide +kernel

theorem rows22000E_1003 : rowsJD 186 187 132 272 ≤ 3447095747182500 := by decide +kernel

theorem rows22000E_1004 : rowsJD 187 188 0 71 ≤ 331795446119448 := by decide +kernel

theorem rows22000E_1005 : rowsJD 187 188 71 81 ≤ 399714918176318 := by decide +kernel

theorem rows22000E_1006 : rowsJD 187 188 81 272 ≤ 6645001333135984 := by decide +kernel

theorem rows22000E_1007 : rowsJD 188 189 0 71 ≤ 366675304565628 := by decide +kernel

theorem rows22000E_1008 : rowsJD 188 189 71 81 ≤ 431120873800687 := by decide +kernel

theorem rows22000E_1009 : rowsJD 188 189 81 272 ≤ 6620446669005128 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1000
#print axioms SieveDeep.rows22000E_1009
