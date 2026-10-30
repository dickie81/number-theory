/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 460–469 of 1136

File 47 of 114: the parts `rows22000E_460` … `rows22000E_469` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 263 s of the kernel: row 107 columns 99–102, row 107 columns
103–105, row 107 columns 106–271, row 108 columns 0–39, row 108 columns 40–56, row 108 columns 57–68, row 108
columns 69–76, row 108 columns 77–84, row 108 columns 85–90, row 108 columns 91–95), each a sum of the costs
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

theorem rows22000E_460 : rowsJD 107 108 99 103 ≤ 180162646022203 := by decide +kernel

theorem rows22000E_461 : rowsJD 107 108 103 106 ≤ 178048023761592 := by decide +kernel

theorem rows22000E_462 : rowsJD 107 108 106 272 ≤ 68881320973111 := by decide +kernel

theorem rows22000E_463 : rowsJD 108 109 0 40 ≤ 145556367829072 := by decide +kernel

theorem rows22000E_464 : rowsJD 108 109 40 57 ≤ 160220395424693 := by decide +kernel

theorem rows22000E_465 : rowsJD 108 109 57 69 ≤ 94468829258354 := by decide +kernel

theorem rows22000E_466 : rowsJD 108 109 69 77 ≤ 39103303027978 := by decide +kernel

theorem rows22000E_467 : rowsJD 108 109 77 85 ≤ 37070526101938 := by decide +kernel

theorem rows22000E_468 : rowsJD 108 109 85 91 ≤ 47902460688344 := by decide +kernel

theorem rows22000E_469 : rowsJD 108 109 91 96 ≤ 97368196021781 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_460
#print axioms SieveDeep.rows22000E_469
