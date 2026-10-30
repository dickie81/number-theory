/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 890–899 of 1136

File 90 of 114: the parts `rows22000E_890` … `rows22000E_899` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 280 s of the kernel: row 164 columns 90–97, row 164 columns
98–102, row 164 columns 103–271, row 165 columns 0–43, row 165 columns 44–77, row 165 columns 78–89, row 165 columns
90–97, row 165 columns 98–102, row 165 columns 103–271, row 166 columns 0–42), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_890 : rowsJD 164 165 90 98 ≤ 391119802011072 := by decide +kernel

theorem rows22000E_891 : rowsJD 164 165 98 103 ≤ 409890813124785 := by decide +kernel

theorem rows22000E_892 : rowsJD 164 165 103 272 ≤ 4247317404237549 := by decide +kernel

theorem rows22000E_893 : rowsJD 165 166 0 44 ≤ 24626557842362 := by decide +kernel

theorem rows22000E_894 : rowsJD 165 166 44 78 ≤ 383963188092353 := by decide +kernel

theorem rows22000E_895 : rowsJD 165 166 78 90 ≤ 620573392247678 := by decide +kernel

theorem rows22000E_896 : rowsJD 165 166 90 98 ≤ 384767772031511 := by decide +kernel

theorem rows22000E_897 : rowsJD 165 166 98 103 ≤ 393878993489581 := by decide +kernel

theorem rows22000E_898 : rowsJD 165 166 103 272 ≤ 4304791981507004 := by decide +kernel

theorem rows22000E_899 : rowsJD 166 167 0 43 ≤ 23936858405007 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_890
#print axioms SieveDeep.rows22000E_899
