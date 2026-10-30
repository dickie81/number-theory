/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 810–819 of 1136

File 82 of 114: the parts `rows22000E_810` … `rows22000E_819` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 272 s of the kernel: row 153 columns 112–271, row 154 columns
0–45, row 154 columns 46–57, row 154 columns 58–87, row 154 columns 88–95, row 154 columns 96–101, row 154 columns
102–106, row 154 columns 107–111, row 154 columns 112–271, row 155 columns 0–45), each a sum of the costs (`rowsJD`)
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

theorem rows22000E_810 : rowsJD 153 154 112 272 ≤ 2212047525065534 := by decide +kernel

theorem rows22000E_811 : rowsJD 154 155 0 46 ≤ 33971645255039 := by decide +kernel

theorem rows22000E_812 : rowsJD 154 155 46 58 ≤ 19715626558030 := by decide +kernel

theorem rows22000E_813 : rowsJD 154 155 58 88 ≤ 343636384347888 := by decide +kernel

theorem rows22000E_814 : rowsJD 154 155 88 96 ≤ 406641605348429 := by decide +kernel

theorem rows22000E_815 : rowsJD 154 155 96 102 ≤ 482191489178693 := by decide +kernel

theorem rows22000E_816 : rowsJD 154 155 102 107 ≤ 425395732009387 := by decide +kernel

theorem rows22000E_817 : rowsJD 154 155 107 112 ≤ 363264512508702 := by decide +kernel

theorem rows22000E_818 : rowsJD 154 155 112 272 ≤ 2289882380375695 := by decide +kernel

theorem rows22000E_819 : rowsJD 155 156 0 46 ≤ 31928895764561 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_810
#print axioms SieveDeep.rows22000E_819
