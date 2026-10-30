/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 720–729 of 1136

File 73 of 114: the parts `rows22000E_720` … `rows22000E_729` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 244 s of the kernel: row 141 columns 121–271, row 142 columns
0–47, row 142 columns 48–60, row 142 columns 61–89, row 142 columns 90–98, row 142 columns 99–107, row 142 columns
108–118, row 142 columns 119–271, row 143 columns 0–47, row 143 columns 48–60), each a sum of the costs (`rowsJD`)
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

theorem rows22000E_720 : rowsJD 141 142 121 272 ≤ 831853865792623 := by decide +kernel

theorem rows22000E_721 : rowsJD 142 143 0 48 ≤ 71729532262729 := by decide +kernel

theorem rows22000E_722 : rowsJD 142 143 48 61 ≤ 25155879682286 := by decide +kernel

theorem rows22000E_723 : rowsJD 142 143 61 90 ≤ 236997581910573 := by decide +kernel

theorem rows22000E_724 : rowsJD 142 143 90 99 ≤ 352736037517204 := by decide +kernel

theorem rows22000E_725 : rowsJD 142 143 99 108 ≤ 387141138459799 := by decide +kernel

theorem rows22000E_726 : rowsJD 142 143 108 119 ≤ 660868030525507 := by decide +kernel

theorem rows22000E_727 : rowsJD 142 143 119 272 ≤ 939645600907435 := by decide +kernel

theorem rows22000E_728 : rowsJD 143 144 0 48 ≤ 68735815152298 := by decide +kernel

theorem rows22000E_729 : rowsJD 143 144 48 61 ≤ 23145565694301 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_720
#print axioms SieveDeep.rows22000E_729
