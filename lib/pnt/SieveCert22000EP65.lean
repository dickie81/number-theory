/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 640–649 of 1136

File 65 of 114: the parts `rows22000E_640` … `rows22000E_649` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 279 s of the kernel: row 130 columns 73–79, row 130 columns
80–103, row 130 columns 104–111, row 130 columns 112–271, row 131 columns 0–47, row 131 columns 48–61, row 131
columns 62–72, row 131 columns 73–79, row 131 columns 80–103, row 131 columns 104–111), each a sum of the costs
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

theorem rows22000E_640 : rowsJD 130 131 73 80 ≤ 274460626180012 := by decide +kernel

theorem rows22000E_641 : rowsJD 130 131 80 104 ≤ 285099814547171 := by decide +kernel

theorem rows22000E_642 : rowsJD 130 131 104 112 ≤ 328721476093284 := by decide +kernel

theorem rows22000E_643 : rowsJD 130 131 112 272 ≤ 1863114335455325 := by decide +kernel

theorem rows22000E_644 : rowsJD 131 132 0 48 ≤ 113748639136219 := by decide +kernel

theorem rows22000E_645 : rowsJD 131 132 48 62 ≤ 73407963326164 := by decide +kernel

theorem rows22000E_646 : rowsJD 131 132 62 73 ≤ 92725512233817 := by decide +kernel

theorem rows22000E_647 : rowsJD 131 132 73 80 ≤ 287489013906754 := by decide +kernel

theorem rows22000E_648 : rowsJD 131 132 80 104 ≤ 276842316629347 := by decide +kernel

theorem rows22000E_649 : rowsJD 131 132 104 112 ≤ 348009727993768 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_640
#print axioms SieveDeep.rows22000E_649
