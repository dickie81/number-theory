/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 790–799 of 1136

File 80 of 114: the parts `rows22000E_790` … `rows22000E_799` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 271 s of the kernel: row 151 columns 88–95, row 151 columns
96–102, row 151 columns 103–108, row 151 columns 109–114, row 151 columns 115–271, row 152 columns 0–46, row 152
columns 47–58, row 152 columns 59–87, row 152 columns 88–95, row 152 columns 96–102), each a sum of the costs
(`rowsJD`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_790 : rowsJD 151 152 88 96 ≤ 463230451280293 := by decide +kernel

theorem rows22000E_791 : rowsJD 151 152 96 103 ≤ 510932775257404 := by decide +kernel

theorem rows22000E_792 : rowsJD 151 152 103 109 ≤ 436991223647813 := by decide +kernel

theorem rows22000E_793 : rowsJD 151 152 109 115 ≤ 411752945234810 := by decide +kernel

theorem rows22000E_794 : rowsJD 151 152 115 272 ≤ 1837723621131815 := by decide +kernel

theorem rows22000E_795 : rowsJD 152 153 0 47 ≤ 39299862850989 := by decide +kernel

theorem rows22000E_796 : rowsJD 152 153 47 59 ≤ 18697276943692 := by decide +kernel

theorem rows22000E_797 : rowsJD 152 153 59 88 ≤ 284804098865539 := by decide +kernel

theorem rows22000E_798 : rowsJD 152 153 88 96 ≤ 451955964571249 := by decide +kernel

theorem rows22000E_799 : rowsJD 152 153 96 103 ≤ 543978631516146 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_790
#print axioms SieveDeep.rows22000E_799
