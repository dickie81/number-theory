/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 940–949 of 1136

File 95 of 114: the parts `rows22000E_940` … `rows22000E_949` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 262 s of the kernel: row 173 columns 80–88, row 173 columns 89–95,
row 173 columns 96–271, row 174 columns 0–63, row 174 columns 64–79, row 174 columns 80–88, row 174 columns 89–113,
row 174 columns 114–271, row 175 columns 0–64, row 175 columns 65–79), each a sum of the costs (`rowsJD`) at most
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

theorem rows22000E_940 : rowsJD 173 174 80 89 ≤ 682127250739839 := by decide +kernel

theorem rows22000E_941 : rowsJD 173 174 89 96 ≤ 721402793409905 := by decide +kernel

theorem rows22000E_942 : rowsJD 173 174 96 272 ≤ 5698409458007948 := by decide +kernel

theorem rows22000E_943 : rowsJD 174 175 0 64 ≤ 132329216863108 := by decide +kernel

theorem rows22000E_944 : rowsJD 174 175 64 80 ≤ 700553270508081 := by decide +kernel

theorem rows22000E_945 : rowsJD 174 175 80 89 ≤ 691162625607130 := by decide +kernel

theorem rows22000E_946 : rowsJD 174 175 89 114 ≤ 741143030741225 := by decide +kernel

theorem rows22000E_947 : rowsJD 174 175 114 272 ≤ 5785348918247485 := by decide +kernel

theorem rows22000E_948 : rowsJD 175 176 0 65 ≤ 171819301177787 := by decide +kernel

theorem rows22000E_949 : rowsJD 175 176 65 80 ≤ 617610279775446 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_940
#print axioms SieveDeep.rows22000E_949
