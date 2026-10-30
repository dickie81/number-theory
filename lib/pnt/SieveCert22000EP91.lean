/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 900–909 of 1136

File 91 of 114: the parts `rows22000E_900` … `rows22000E_909` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 273 s of the kernel: row 166 columns 43–76, row 166 columns 77–88,
row 166 columns 89–96, row 166 columns 97–101, row 166 columns 102–271, row 167 columns 0–42, row 167 columns 43–77,
row 167 columns 78–88, row 167 columns 89–96, row 167 columns 97–101), each a sum of the costs (`rowsJD`) at most
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

theorem rows22000E_900 : rowsJD 166 167 43 77 ≤ 386665750743766 := by decide +kernel

theorem rows22000E_901 : rowsJD 166 167 77 89 ≤ 676920463207809 := by decide +kernel

theorem rows22000E_902 : rowsJD 166 167 89 97 ≤ 379950276524824 := by decide +kernel

theorem rows22000E_903 : rowsJD 166 167 97 102 ≤ 341356309746261 := by decide +kernel

theorem rows22000E_904 : rowsJD 166 167 102 272 ≤ 4467670953940493 := by decide +kernel

theorem rows22000E_905 : rowsJD 167 168 0 43 ≤ 24498694656822 := by decide +kernel

theorem rows22000E_906 : rowsJD 167 168 43 78 ≤ 506437919850020 := by decide +kernel

theorem rows22000E_907 : rowsJD 167 168 78 89 ≤ 659128829884868 := by decide +kernel

theorem rows22000E_908 : rowsJD 167 168 89 97 ≤ 401183261600991 := by decide +kernel

theorem rows22000E_909 : rowsJD 167 168 97 102 ≤ 326485610084963 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_900
#print axioms SieveDeep.rows22000E_909
