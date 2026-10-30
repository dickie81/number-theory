/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 610–619 of 1136

File 62 of 114: the parts `rows22000E_610` … `rows22000E_619` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 284 s of the kernel: row 126 columns 46–61, row 126 columns 62–72,
row 126 columns 73–79, row 126 columns 80–84, row 126 columns 85–109, row 126 columns 110–271, row 127 columns 0–45,
row 127 columns 46–61, row 127 columns 62–72, row 127 columns 73–79), each a sum of the costs (`rowsJD`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_610 : rowsJD 126 127 46 62 ≤ 96321286688559 := by decide +kernel

theorem rows22000E_611 : rowsJD 126 127 62 73 ≤ 77792551029267 := by decide +kernel

theorem rows22000E_612 : rowsJD 126 127 73 80 ≤ 205983048436455 := by decide +kernel

theorem rows22000E_613 : rowsJD 126 127 80 85 ≤ 219562273958004 := by decide +kernel

theorem rows22000E_614 : rowsJD 126 127 85 110 ≤ 232413745929299 := by decide +kernel

theorem rows22000E_615 : rowsJD 126 127 110 272 ≤ 1561051232627932 := by decide +kernel

theorem rows22000E_616 : rowsJD 127 128 0 46 ≤ 134469604163641 := by decide +kernel

theorem rows22000E_617 : rowsJD 127 128 46 62 ≤ 92201672032998 := by decide +kernel

theorem rows22000E_618 : rowsJD 127 128 62 73 ≤ 77522419016256 := by decide +kernel

theorem rows22000E_619 : rowsJD 127 128 73 80 ≤ 224712269273999 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_610
#print axioms SieveDeep.rows22000E_619
