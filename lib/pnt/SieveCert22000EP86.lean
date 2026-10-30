/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 850–859 of 1136

File 86 of 114: the parts `rows22000E_850` … `rows22000E_859` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 250 s of the kernel: row 158 columns 110–271, row 159 columns
0–44, row 159 columns 45–76, row 159 columns 77–88, row 159 columns 89–96, row 159 columns 97–101, row 159 columns
102–105, row 159 columns 106–109, row 159 columns 110–271, row 160 columns 0–44), each a sum of the costs (`rowsJD`)
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

theorem rows22000E_850 : rowsJD 158 159 110 272 ≤ 2939685721865155 := by decide +kernel

theorem rows22000E_851 : rowsJD 159 160 0 45 ≤ 26093746742840 := by decide +kernel

theorem rows22000E_852 : rowsJD 159 160 45 77 ≤ 97146061403573 := by decide +kernel

theorem rows22000E_853 : rowsJD 159 160 77 89 ≤ 506422841017353 := by decide +kernel

theorem rows22000E_854 : rowsJD 159 160 89 97 ≤ 388567921691605 := by decide +kernel

theorem rows22000E_855 : rowsJD 159 160 97 102 ≤ 404513060730440 := by decide +kernel

theorem rows22000E_856 : rowsJD 159 160 102 106 ≤ 457886704576112 := by decide +kernel

theorem rows22000E_857 : rowsJD 159 160 106 110 ≤ 442520790002591 := by decide +kernel

theorem rows22000E_858 : rowsJD 159 160 110 272 ≤ 3055240786893484 := by decide +kernel

theorem rows22000E_859 : rowsJD 160 161 0 45 ≤ 25833616828246 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_850
#print axioms SieveDeep.rows22000E_859
