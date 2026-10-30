/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 620–629 of 1136

File 63 of 114: the parts `rows22000E_620` … `rows22000E_629` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 280 s of the kernel: row 127 columns 80–84, row 127 columns
85–109, row 127 columns 110–271, row 128 columns 0–46, row 128 columns 47–61, row 128 columns 62–72, row 128 columns
73–79, row 128 columns 80–84, row 128 columns 85–110, row 128 columns 111–271), each a sum of the costs (`rowsJD`)
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

theorem rows22000E_620 : rowsJD 127 128 80 85 ≤ 231576330478765 := by decide +kernel

theorem rows22000E_621 : rowsJD 127 128 85 110 ≤ 248351427447634 := by decide +kernel

theorem rows22000E_622 : rowsJD 127 128 110 272 ≤ 1650389442305352 := by decide +kernel

theorem rows22000E_623 : rowsJD 128 129 0 47 ≤ 131891920856184 := by decide +kernel

theorem rows22000E_624 : rowsJD 128 129 47 62 ≤ 86649468358654 := by decide +kernel

theorem rows22000E_625 : rowsJD 128 129 62 73 ≤ 79316177949146 := by decide +kernel

theorem rows22000E_626 : rowsJD 128 129 73 80 ≤ 242444764870114 := by decide +kernel

theorem rows22000E_627 : rowsJD 128 129 80 85 ≤ 242696522055978 := by decide +kernel

theorem rows22000E_628 : rowsJD 128 129 85 111 ≤ 293341236663008 := by decide +kernel

theorem rows22000E_629 : rowsJD 128 129 111 272 ≤ 1717883811448767 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_620
#print axioms SieveDeep.rows22000E_629
