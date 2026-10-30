/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 20–29 of 1136

File 3 of 114: the parts `rows22000E_20` … `rows22000E_29` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 225 s of the kernel: row 40 columns 0–36, row 40 columns 37–271,
row 41 columns 0–36, row 41 columns 37–271, row 42 columns 0–36, row 42 columns 37–271, row 43 columns 0–36, row 43
columns 37–271, row 44 columns 0–36, row 44 columns 37–271), each a sum of the costs (`rowsJD`) at most its bound,
by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_20 : rowsJD 40 41 0 37 ≤ 360115107546945 := by decide +kernel

theorem rows22000E_21 : rowsJD 40 41 37 272 ≤ 119362363050814 := by decide +kernel

theorem rows22000E_22 : rowsJD 41 42 0 37 ≤ 352863264453583 := by decide +kernel

theorem rows22000E_23 : rowsJD 41 42 37 272 ≤ 156709197232761 := by decide +kernel

theorem rows22000E_24 : rowsJD 42 43 0 37 ≤ 346344864594059 := by decide +kernel

theorem rows22000E_25 : rowsJD 42 43 37 272 ≤ 193210673926635 := by decide +kernel

theorem rows22000E_26 : rowsJD 43 44 0 37 ≤ 340779564944929 := by decide +kernel

theorem rows22000E_27 : rowsJD 43 44 37 272 ≤ 228254550366019 := by decide +kernel

theorem rows22000E_28 : rowsJD 44 45 0 37 ≤ 336001590527156 := by decide +kernel

theorem rows22000E_29 : rowsJD 44 45 37 272 ≤ 265028982656651 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_20
#print axioms SieveDeep.rows22000E_29
