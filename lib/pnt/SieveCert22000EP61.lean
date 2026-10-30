/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 600–609 of 1136

File 61 of 114: the parts `rows22000E_600` … `rows22000E_609` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 259 s of the kernel: row 124 columns 110–271, row 125 columns
0–44, row 125 columns 45–61, row 125 columns 62–72, row 125 columns 73–79, row 125 columns 80–84, row 125 columns
85–108, row 125 columns 109–120, row 125 columns 121–271, row 126 columns 0–45), each a sum of the costs (`rowsJD`)
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

theorem rows22000E_600 : rowsJD 124 125 110 272 ≤ 1394927929836588 := by decide +kernel

theorem rows22000E_601 : rowsJD 125 126 0 45 ≤ 141854093258163 := by decide +kernel

theorem rows22000E_602 : rowsJD 125 126 45 62 ≤ 103138421829664 := by decide +kernel

theorem rows22000E_603 : rowsJD 125 126 62 73 ≤ 82442480674207 := by decide +kernel

theorem rows22000E_604 : rowsJD 125 126 73 80 ≤ 186626169372001 := by decide +kernel

theorem rows22000E_605 : rowsJD 125 126 80 85 ≤ 207340629466550 := by decide +kernel

theorem rows22000E_606 : rowsJD 125 126 85 109 ≤ 208579346269225 := by decide +kernel

theorem rows22000E_607 : rowsJD 125 126 109 121 ≤ 928404139285035 := by decide +kernel

theorem rows22000E_608 : rowsJD 125 126 121 272 ≤ 573696863229619 := by decide +kernel

theorem rows22000E_609 : rowsJD 126 127 0 46 ≤ 140009622572679 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_600
#print axioms SieveDeep.rows22000E_609
