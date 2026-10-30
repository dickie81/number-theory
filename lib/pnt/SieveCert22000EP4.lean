/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 30–39 of 1136

File 4 of 114: the parts `rows22000E_30` … `rows22000E_39` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 238 s of the kernel: row 45 columns 0–36, row 45 columns 37–271,
row 46 columns 0–36, row 46 columns 37–271, row 47 columns 0–36, row 47 columns 37–46, row 47 columns 47–271, row 48
columns 0–36, row 48 columns 37–46, row 48 columns 47–271), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_30 : rowsJD 45 46 0 37 ≤ 332086196980064 := by decide +kernel

theorem rows22000E_31 : rowsJD 45 46 37 272 ≤ 302437201150450 := by decide +kernel

theorem rows22000E_32 : rowsJD 46 47 0 37 ≤ 328327876634190 := by decide +kernel

theorem rows22000E_33 : rowsJD 46 47 37 272 ≤ 337689153957225 := by decide +kernel

theorem rows22000E_34 : rowsJD 47 48 0 37 ≤ 324291710439470 := by decide +kernel

theorem rows22000E_35 : rowsJD 47 48 37 47 ≤ 331847754334252 := by decide +kernel

theorem rows22000E_36 : rowsJD 47 48 47 272 ≤ 37987633600343 := by decide +kernel

theorem rows22000E_37 : rowsJD 48 49 0 37 ≤ 320001567448610 := by decide +kernel

theorem rows22000E_38 : rowsJD 48 49 37 47 ≤ 326272609859958 := by decide +kernel

theorem rows22000E_39 : rowsJD 48 49 47 272 ≤ 73534029704815 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_30
#print axioms SieveDeep.rows22000E_39
