/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 590–599 of 1136

File 60 of 114: the parts `rows22000E_590` … `rows22000E_599` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 261 s of the kernel: row 123 columns 80–85, row 123 columns
86–108, row 123 columns 109–117, row 123 columns 118–271, row 124 columns 0–43, row 124 columns 44–61, row 124
columns 62–72, row 124 columns 73–79, row 124 columns 80–85, row 124 columns 86–109), each a sum of the costs
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

theorem rows22000E_590 : rowsJD 123 124 80 86 ≤ 219924301847768 := by decide +kernel

theorem rows22000E_591 : rowsJD 123 124 86 109 ≤ 174543533096115 := by decide +kernel

theorem rows22000E_592 : rowsJD 123 124 109 118 ≤ 607846558776910 := by decide +kernel

theorem rows22000E_593 : rowsJD 123 124 118 272 ≤ 740886412025844 := by decide +kernel

theorem rows22000E_594 : rowsJD 124 125 0 44 ≤ 143594022571143 := by decide +kernel

theorem rows22000E_595 : rowsJD 124 125 44 62 ≤ 111591708052309 := by decide +kernel

theorem rows22000E_596 : rowsJD 124 125 62 73 ≤ 89181133260176 := by decide +kernel

theorem rows22000E_597 : rowsJD 124 125 73 80 ≤ 167182261707950 := by decide +kernel

theorem rows22000E_598 : rowsJD 124 125 80 86 ≤ 235281427454538 := by decide +kernel

theorem rows22000E_599 : rowsJD 124 125 86 110 ≤ 206371599857659 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_590
#print axioms SieveDeep.rows22000E_599
