/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 820–829 of 1136

File 83 of 114: the parts `rows22000E_820` … `rows22000E_829` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 274 s of the kernel: row 155 columns 46–76, row 155 columns 77–88,
row 155 columns 89–96, row 155 columns 97–102, row 155 columns 103–107, row 155 columns 108–112, row 155 columns
113–271, row 156 columns 0–45, row 156 columns 46–76, row 156 columns 77–88), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_820 : rowsJD 155 156 46 77 ≤ 30633764826833 := by decide +kernel

theorem rows22000E_821 : rowsJD 155 156 77 89 ≤ 410087665942525 := by decide +kernel

theorem rows22000E_822 : rowsJD 155 156 89 97 ≤ 413616385627157 := by decide +kernel

theorem rows22000E_823 : rowsJD 155 156 97 103 ≤ 506380514031537 := by decide +kernel

theorem rows22000E_824 : rowsJD 155 156 103 108 ≤ 440572182883107 := by decide +kernel

theorem rows22000E_825 : rowsJD 155 156 108 113 ≤ 355938461884393 := by decide +kernel

theorem rows22000E_826 : rowsJD 155 156 113 272 ≤ 2337987270496437 := by decide +kernel

theorem rows22000E_827 : rowsJD 156 157 0 46 ≤ 30559025817813 := by decide +kernel

theorem rows22000E_828 : rowsJD 156 157 46 77 ≤ 41943862695203 := by decide +kernel

theorem rows22000E_829 : rowsJD 156 157 77 89 ≤ 438397343743503 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_820
#print axioms SieveDeep.rows22000E_829
