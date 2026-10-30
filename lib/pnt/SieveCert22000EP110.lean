/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 1090–1099 of 1136

File 110 of 114: the parts `rows22000E_1090` … `rows22000E_1099` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 235 s of the kernel: row 220 columns 0–76, row 220 columns 77–271,
row 221 columns 0–75, row 221 columns 76–271, row 222 columns 0–76, row 222 columns 77–271, row 223 columns 0–77,
row 223 columns 78–271, row 224 columns 0–78, row 224 columns 79–271), each a sum of the costs (`rowsJD`) at most
its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_1090 : rowsJD 220 221 0 77 ≤ 2256497960674759 := by decide +kernel

theorem rows22000E_1091 : rowsJD 220 221 77 272 ≤ 8077433566981244 := by decide +kernel

theorem rows22000E_1092 : rowsJD 221 222 0 76 ≤ 2302319454290292 := by decide +kernel

theorem rows22000E_1093 : rowsJD 221 222 76 272 ≤ 8235160722695386 := by decide +kernel

theorem rows22000E_1094 : rowsJD 222 223 0 77 ≤ 2659658998653175 := by decide +kernel

theorem rows22000E_1095 : rowsJD 222 223 77 272 ≤ 7964133572206568 := by decide +kernel

theorem rows22000E_1096 : rowsJD 223 224 0 78 ≤ 3010830834305292 := by decide +kernel

theorem rows22000E_1097 : rowsJD 223 224 78 272 ≤ 7793610483562251 := by decide +kernel

theorem rows22000E_1098 : rowsJD 224 225 0 79 ≤ 3355070999165653 := by decide +kernel

theorem rows22000E_1099 : rowsJD 224 225 79 272 ≤ 7534046568434599 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_1090
#print axioms SieveDeep.rows22000E_1099
