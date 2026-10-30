/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 200–209 of 1136

File 21 of 114: the parts `rows22000E_200` … `rows22000E_209` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 283 s of the kernel: row 79 columns 37–48, row 79 columns 49–55,
row 79 columns 56–62, row 79 columns 63–70, row 79 columns 71–75, row 79 columns 76–271, row 80 columns 0–36, row 80
columns 37–48, row 80 columns 49–55, row 80 columns 56–62), each a sum of the costs (`rowsJD`) at most its bound, by
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

theorem rows22000E_200 : rowsJD 79 80 37 49 ≤ 149806855795436 := by decide +kernel

theorem rows22000E_201 : rowsJD 79 80 49 56 ≤ 85268122439411 := by decide +kernel

theorem rows22000E_202 : rowsJD 79 80 56 63 ≤ 87240532523120 := by decide +kernel

theorem rows22000E_203 : rowsJD 79 80 63 71 ≤ 97092718016312 := by decide +kernel

theorem rows22000E_204 : rowsJD 79 80 71 76 ≤ 68514809055334 := by decide +kernel

theorem rows22000E_205 : rowsJD 79 80 76 272 ≤ 78768832239650 := by decide +kernel

theorem rows22000E_206 : rowsJD 80 81 0 37 ≤ 217656469672816 := by decide +kernel

theorem rows22000E_207 : rowsJD 80 81 37 49 ≤ 145395316101788 := by decide +kernel

theorem rows22000E_208 : rowsJD 80 81 49 56 ≤ 86938783825902 := by decide +kernel

theorem rows22000E_209 : rowsJD 80 81 56 63 ≤ 87694082085350 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_200
#print axioms SieveDeep.rows22000E_209
