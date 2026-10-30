/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 930–939 of 1136

File 94 of 114: the parts `rows22000E_930` … `rows22000E_939` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 272 s of the kernel: row 171 columns 79–88, row 171 columns 89–95,
row 171 columns 96–271, row 172 columns 0–61, row 172 columns 62–79, row 172 columns 80–88, row 172 columns 89–95,
row 172 columns 96–271, row 173 columns 0–62, row 173 columns 63–79), each a sum of the costs (`rowsJD`) at most its
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

theorem rows22000E_930 : rowsJD 171 172 79 89 ≤ 693008113063276 := by decide +kernel

theorem rows22000E_931 : rowsJD 171 172 89 96 ≤ 610029312879829 := by decide +kernel

theorem rows22000E_932 : rowsJD 171 172 96 272 ≤ 5456650684402779 := by decide +kernel

theorem rows22000E_933 : rowsJD 172 173 0 62 ≤ 50718409317463 := by decide +kernel

theorem rows22000E_934 : rowsJD 172 173 62 80 ≤ 805455823513785 := by decide +kernel

theorem rows22000E_935 : rowsJD 172 173 80 89 ≤ 655366978267097 := by decide +kernel

theorem rows22000E_936 : rowsJD 172 173 89 96 ≤ 666019858786660 := by decide +kernel

theorem rows22000E_937 : rowsJD 172 173 96 272 ≤ 5589578682370895 := by decide +kernel

theorem rows22000E_938 : rowsJD 173 174 0 63 ≤ 87736630301224 := by decide +kernel

theorem rows22000E_939 : rowsJD 173 174 63 80 ≤ 774852411497733 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_930
#print axioms SieveDeep.rows22000E_939
