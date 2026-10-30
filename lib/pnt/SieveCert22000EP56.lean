/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 550–559 of 1136

File 56 of 114: the parts `rows22000E_550` … `rows22000E_559` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 251 s of the kernel: row 118 columns 81–86, row 118 columns 87–91,
row 118 columns 92–114, row 118 columns 115–271, row 119 columns 0–40, row 119 columns 41–60, row 119 columns 61–69,
row 119 columns 70–79, row 119 columns 80–85, row 119 columns 86–90), each a sum of the costs (`rowsJD`) at most its
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

theorem rows22000E_550 : rowsJD 118 119 81 87 ≤ 142321575956336 := by decide +kernel

theorem rows22000E_551 : rowsJD 118 119 87 92 ≤ 131045819674637 := by decide +kernel

theorem rows22000E_552 : rowsJD 118 119 92 115 ≤ 197057884119803 := by decide +kernel

theorem rows22000E_553 : rowsJD 118 119 115 272 ≤ 521826399732959 := by decide +kernel

theorem rows22000E_554 : rowsJD 119 120 0 41 ≤ 145538295251878 := by decide +kernel

theorem rows22000E_555 : rowsJD 119 120 41 61 ≤ 138852370973528 := by decide +kernel

theorem rows22000E_556 : rowsJD 119 120 61 70 ≤ 144389748549604 := by decide +kernel

theorem rows22000E_557 : rowsJD 119 120 70 80 ≤ 113682866675308 := by decide +kernel

theorem rows22000E_558 : rowsJD 119 120 80 86 ≤ 152784371734761 := by decide +kernel

theorem rows22000E_559 : rowsJD 119 120 86 91 ≤ 141493204718791 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_550
#print axioms SieveDeep.rows22000E_559
