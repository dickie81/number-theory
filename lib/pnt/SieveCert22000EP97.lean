/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 960–969 of 1136

File 97 of 114: the parts `rows22000E_960` … `rows22000E_969` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 267 s of the kernel: row 177 columns 80–87, row 177 columns
88–112, row 177 columns 113–271, row 178 columns 0–66, row 178 columns 67–80, row 178 columns 81–88, row 178 columns
89–113, row 178 columns 114–271, row 179 columns 0–67, row 179 columns 68–80), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_960 : rowsJD 177 178 80 88 ≤ 604286679194372 := by decide +kernel

theorem rows22000E_961 : rowsJD 177 178 88 113 ≤ 676837062435256 := by decide +kernel

theorem rows22000E_962 : rowsJD 177 178 113 272 ≤ 5784214278519966 := by decide +kernel

theorem rows22000E_963 : rowsJD 178 179 0 67 ≤ 174218218423099 := by decide +kernel

theorem rows22000E_964 : rowsJD 178 179 67 81 ≤ 499393818734934 := by decide +kernel

theorem rows22000E_965 : rowsJD 178 179 81 89 ≤ 626341032489052 := by decide +kernel

theorem rows22000E_966 : rowsJD 178 179 89 114 ≤ 640060657456799 := by decide +kernel

theorem rows22000E_967 : rowsJD 178 179 114 272 ≤ 5588926386857574 := by decide +kernel

theorem rows22000E_968 : rowsJD 179 180 0 68 ≤ 163617321989972 := by decide +kernel

theorem rows22000E_969 : rowsJD 179 180 68 81 ≤ 450219395089713 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_960
#print axioms SieveDeep.rows22000E_969
