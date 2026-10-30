/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 910–919 of 1136

File 92 of 114: the parts `rows22000E_910` … `rows22000E_919` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 256 s of the kernel: row 167 columns 102–271, row 168 columns
0–42, row 168 columns 43–77, row 168 columns 78–88, row 168 columns 89–96, row 168 columns 97–131, row 168 columns
132–271, row 169 columns 0–42, row 169 columns 43–78, row 169 columns 79–89), each a sum of the costs (`rowsJD`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_910 : rowsJD 167 168 102 272 ≤ 4552944127573445 := by decide +kernel

theorem rows22000E_911 : rowsJD 168 169 0 43 ≤ 25755824037966 := by decide +kernel

theorem rows22000E_912 : rowsJD 168 169 43 78 ≤ 563259516446568 := by decide +kernel

theorem rows22000E_913 : rowsJD 168 169 78 89 ≤ 701109164040601 := by decide +kernel

theorem rows22000E_914 : rowsJD 168 169 89 97 ≤ 451575888815827 := by decide +kernel

theorem rows22000E_915 : rowsJD 168 169 97 132 ≤ 1498296124711472 := by decide +kernel

theorem rows22000E_916 : rowsJD 168 169 132 272 ≤ 3472228804783939 := by decide +kernel

theorem rows22000E_917 : rowsJD 169 170 0 43 ≤ 27000661917097 := by decide +kernel

theorem rows22000E_918 : rowsJD 169 170 43 79 ≤ 678778811163515 := by decide +kernel

theorem rows22000E_919 : rowsJD 169 170 79 90 ≤ 715228167362849 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_910
#print axioms SieveDeep.rows22000E_919
