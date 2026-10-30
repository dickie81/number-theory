/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 730–739 of 1136

File 74 of 114: the parts `rows22000E_730` … `rows22000E_739` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 268 s of the kernel: row 143 columns 61–89, row 143 columns 90–97,
row 143 columns 98–106, row 143 columns 107–114, row 143 columns 115–271, row 144 columns 0–47, row 144 columns
48–59, row 144 columns 60–89, row 144 columns 90–97, row 144 columns 98–105), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_730 : rowsJD 143 144 61 90 ≤ 278203390581834 := by decide +kernel

theorem rows22000E_731 : rowsJD 143 144 90 98 ≤ 367238613446806 := by decide +kernel

theorem rows22000E_732 : rowsJD 143 144 98 107 ≤ 422921928250120 := by decide +kernel

theorem rows22000E_733 : rowsJD 143 144 107 115 ≤ 360300169943337 := by decide +kernel

theorem rows22000E_734 : rowsJD 143 144 115 272 ≤ 1221249705292336 := by decide +kernel

theorem rows22000E_735 : rowsJD 144 145 0 48 ≤ 66039081082339 := by decide +kernel

theorem rows22000E_736 : rowsJD 144 145 48 60 ≤ 20281348778742 := by decide +kernel

theorem rows22000E_737 : rowsJD 144 145 60 90 ≤ 304979689481339 := by decide +kernel

theorem rows22000E_738 : rowsJD 144 145 90 98 ≤ 421781274472720 := by decide +kernel

theorem rows22000E_739 : rowsJD 144 145 98 106 ≤ 419098217897672 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_730
#print axioms SieveDeep.rows22000E_739
