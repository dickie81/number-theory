/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 50–59 of 1136

File 6 of 114: the parts `rows22000E_50` … `rows22000E_59` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 272 s of the kernel: row 52 columns 37–46, row 52 columns 47–271,
row 53 columns 0–36, row 53 columns 37–46, row 53 columns 47–271, row 54 columns 0–36, row 54 columns 37–46, row 54
columns 47–271, row 55 columns 0–36, row 55 columns 37–46), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_50 : rowsJD 52 53 37 47 ≤ 305032766527140 := by decide +kernel

theorem rows22000E_51 : rowsJD 52 53 47 272 ≤ 187409244975853 := by decide +kernel

theorem rows22000E_52 : rowsJD 53 54 0 37 ≤ 301010843057417 := by decide +kernel

theorem rows22000E_53 : rowsJD 53 54 37 47 ≤ 298919842087794 := by decide +kernel

theorem rows22000E_54 : rowsJD 53 54 47 272 ≤ 208053984768068 := by decide +kernel

theorem rows22000E_55 : rowsJD 54 55 0 37 ≤ 298250909607714 := by decide +kernel

theorem rows22000E_56 : rowsJD 54 55 37 47 ≤ 292790446378639 := by decide +kernel

theorem rows22000E_57 : rowsJD 54 55 47 272 ≤ 225180922248018 := by decide +kernel

theorem rows22000E_58 : rowsJD 55 56 0 37 ≤ 294341805553280 := by decide +kernel

theorem rows22000E_59 : rowsJD 55 56 37 47 ≤ 285391086688209 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_50
#print axioms SieveDeep.rows22000E_59
