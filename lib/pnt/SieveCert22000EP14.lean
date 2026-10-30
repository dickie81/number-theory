/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 130–139 of 1136

File 14 of 114: the parts `rows22000E_130` … `rows22000E_139` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 251 s of the kernel: row 69 columns 0–36, row 69 columns 37–47,
row 69 columns 48–54, row 69 columns 55–59, row 69 columns 60–63, row 69 columns 64–68, row 69 columns 69–271, row
70 columns 0–36, row 70 columns 37–47, row 70 columns 48–54), each a sum of the costs (`rowsJD`) at most its bound,
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

theorem rows22000E_130 : rowsJD 69 70 0 37 ≤ 251384221553714 := by decide +kernel

theorem rows22000E_131 : rowsJD 69 70 37 48 ≤ 206164829563109 := by decide +kernel

theorem rows22000E_132 : rowsJD 69 70 48 55 ≤ 97963962104088 := by decide +kernel

theorem rows22000E_133 : rowsJD 69 70 55 60 ≤ 64753801031064 := by decide +kernel

theorem rows22000E_134 : rowsJD 69 70 60 64 ≤ 55570672463399 := by decide +kernel

theorem rows22000E_135 : rowsJD 69 70 64 69 ≤ 61566992561531 := by decide +kernel

theorem rows22000E_136 : rowsJD 69 70 69 272 ≤ 12297041743466 := by decide +kernel

theorem rows22000E_137 : rowsJD 70 71 0 37 ≤ 248555341095384 := by decide +kernel

theorem rows22000E_138 : rowsJD 70 71 37 48 ≤ 198427992342716 := by decide +kernel

theorem rows22000E_139 : rowsJD 70 71 48 55 ≤ 94611625230546 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_130
#print axioms SieveDeep.rows22000E_139
