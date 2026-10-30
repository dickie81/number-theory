/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 740–749 of 1136

File 75 of 114: the parts `rows22000E_740` … `rows22000E_749` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 265 s of the kernel: row 144 columns 106–113, row 144 columns
114–271, row 145 columns 0–47, row 145 columns 48–59, row 145 columns 60–88, row 145 columns 89–96, row 145 columns
97–104, row 145 columns 105–111, row 145 columns 112–271, row 146 columns 0–47), each a sum of the costs (`rowsJD`)
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

theorem rows22000E_740 : rowsJD 144 145 106 114 ≤ 399939986546862 := by decide +kernel

theorem rows22000E_741 : rowsJD 144 145 114 272 ≤ 1270451806354028 := by decide +kernel

theorem rows22000E_742 : rowsJD 145 146 0 48 ≤ 62743575515337 := by decide +kernel

theorem rows22000E_743 : rowsJD 145 146 48 60 ≤ 19805251250667 := by decide +kernel

theorem rows22000E_744 : rowsJD 145 146 60 89 ≤ 283669793338029 := by decide +kernel

theorem rows22000E_745 : rowsJD 145 146 89 97 ≤ 456706934438720 := by decide +kernel

theorem rows22000E_746 : rowsJD 145 146 97 105 ≤ 443324302282459 := by decide +kernel

theorem rows22000E_747 : rowsJD 145 146 105 112 ≤ 376207829576180 := by decide +kernel

theorem rows22000E_748 : rowsJD 145 146 112 272 ≤ 1486639865828571 := by decide +kernel

theorem rows22000E_749 : rowsJD 146 147 0 48 ≤ 59284108442983 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_740
#print axioms SieveDeep.rows22000E_749
