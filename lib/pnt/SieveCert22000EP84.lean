/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 830–839 of 1136

File 84 of 114: the parts `rows22000E_830` … `rows22000E_839` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 264 s of the kernel: row 156 columns 89–96, row 156 columns
97–102, row 156 columns 103–107, row 156 columns 108–112, row 156 columns 113–271, row 157 columns 0–44, row 157
columns 45–75, row 157 columns 76–87, row 157 columns 88–95, row 157 columns 96–101), each a sum of the costs
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

theorem rows22000E_830 : rowsJD 156 157 89 97 ≤ 398450602420874 := by decide +kernel

theorem rows22000E_831 : rowsJD 156 157 97 103 ≤ 504121282960515 := by decide +kernel

theorem rows22000E_832 : rowsJD 156 157 103 108 ≤ 464860863416654 := by decide +kernel

theorem rows22000E_833 : rowsJD 156 157 108 113 ≤ 373464991171844 := by decide +kernel

theorem rows22000E_834 : rowsJD 156 157 113 272 ≤ 2457860078705327 := by decide +kernel

theorem rows22000E_835 : rowsJD 157 158 0 45 ≤ 28003998215039 := by decide +kernel

theorem rows22000E_836 : rowsJD 157 158 45 76 ≤ 40679577780057 := by decide +kernel

theorem rows22000E_837 : rowsJD 157 158 76 88 ≤ 448736967296089 := by decide +kernel

theorem rows22000E_838 : rowsJD 157 158 88 96 ≤ 367421518034886 := by decide +kernel

theorem rows22000E_839 : rowsJD 157 158 96 102 ≤ 463864240249473 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_830
#print axioms SieveDeep.rows22000E_839
