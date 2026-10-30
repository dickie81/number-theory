/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 580–589 of 1136

File 59 of 114: the parts `rows22000E_580` … `rows22000E_589` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 259 s of the kernel: row 122 columns 62–71, row 122 columns 72–79,
row 122 columns 80–85, row 122 columns 86–90, row 122 columns 91–114, row 122 columns 115–271, row 123 columns 0–43,
row 123 columns 44–61, row 123 columns 62–72, row 123 columns 73–79), each a sum of the costs (`rowsJD`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_580 : rowsJD 122 123 62 72 ≤ 106446486294596 := by decide +kernel

theorem rows22000E_581 : rowsJD 122 123 72 80 ≤ 135579693951580 := by decide +kernel

theorem rows22000E_582 : rowsJD 122 123 80 86 ≤ 203588350216371 := by decide +kernel

theorem rows22000E_583 : rowsJD 122 123 86 91 ≤ 168692480320517 := by decide +kernel

theorem rows22000E_584 : rowsJD 122 123 91 115 ≤ 293612693526428 := by decide +kernel

theorem rows22000E_585 : rowsJD 122 123 115 272 ≤ 972348845319236 := by decide +kernel

theorem rows22000E_586 : rowsJD 123 124 0 44 ≤ 148098762719081 := by decide +kernel

theorem rows22000E_587 : rowsJD 123 124 44 62 ≤ 117037996952755 := by decide +kernel

theorem rows22000E_588 : rowsJD 123 124 62 73 ≤ 98563842148395 := by decide +kernel

theorem rows22000E_589 : rowsJD 123 124 73 80 ≤ 148524326372816 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_580
#print axioms SieveDeep.rows22000E_589
