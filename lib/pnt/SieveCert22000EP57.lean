/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 560–569 of 1136

File 57 of 114: the parts `rows22000E_560` … `rows22000E_569` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 244 s of the kernel: row 119 columns 91–113, row 119 columns
114–271, row 120 columns 0–41, row 120 columns 42–61, row 120 columns 62–71, row 120 columns 72–80, row 120 columns
81–86, row 120 columns 87–91, row 120 columns 92–116, row 120 columns 117–271), each a sum of the costs (`rowsJD`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_560 : rowsJD 119 120 91 114 ≤ 186723958833271 := by decide +kernel

theorem rows22000E_561 : rowsJD 119 120 114 272 ≤ 725271347555491 := by decide +kernel

theorem rows22000E_562 : rowsJD 120 121 0 42 ≤ 150083440764652 := by decide +kernel

theorem rows22000E_563 : rowsJD 120 121 42 62 ≤ 142408850227745 := by decide +kernel

theorem rows22000E_564 : rowsJD 120 121 62 72 ≤ 133602611336865 := by decide +kernel

theorem rows22000E_565 : rowsJD 120 121 72 81 ≤ 131352403872117 := by decide +kernel

theorem rows22000E_566 : rowsJD 120 121 81 87 ≤ 175930475847823 := by decide +kernel

theorem rows22000E_567 : rowsJD 120 121 87 92 ≤ 150742694760593 := by decide +kernel

theorem rows22000E_568 : rowsJD 120 121 92 117 ≤ 494256967428197 := by decide +kernel

theorem rows22000E_569 : rowsJD 120 121 117 272 ≤ 528865007300632 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_560
#print axioms SieveDeep.rows22000E_569
