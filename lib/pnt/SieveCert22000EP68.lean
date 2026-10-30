/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 670–679 of 1136

File 68 of 114: the parts `rows22000E_670` … `rows22000E_679` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 258 s of the kernel: row 134 columns 106–114, row 134 columns
115–271, row 135 columns 0–47, row 135 columns 48–61, row 135 columns 62–72, row 135 columns 73–97, row 135 columns
98–105, row 135 columns 106–115, row 135 columns 116–271, row 136 columns 0–47), each a sum of the costs (`rowsJD`)
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

theorem rows22000E_670 : rowsJD 134 135 106 115 ≤ 405536016111693 := by decide +kernel

theorem rows22000E_671 : rowsJD 134 135 115 272 ≤ 2103336337959647 := by decide +kernel

theorem rows22000E_672 : rowsJD 135 136 0 48 ≤ 95382094324651 := by decide +kernel

theorem rows22000E_673 : rowsJD 135 136 48 62 ≤ 53450142958677 := by decide +kernel

theorem rows22000E_674 : rowsJD 135 136 62 73 ≤ 114859680049206 := by decide +kernel

theorem rows22000E_675 : rowsJD 135 136 73 98 ≤ 271834112472658 := by decide +kernel

theorem rows22000E_676 : rowsJD 135 136 98 106 ≤ 298508102436506 := by decide +kernel

theorem rows22000E_677 : rowsJD 135 136 106 116 ≤ 438667978379398 := by decide +kernel

theorem rows22000E_678 : rowsJD 135 136 116 272 ≤ 2052585928767222 := by decide +kernel

theorem rows22000E_679 : rowsJD 136 137 0 48 ≤ 91732273425176 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_670
#print axioms SieveDeep.rows22000E_679
