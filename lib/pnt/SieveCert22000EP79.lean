/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 780–789 of 1136

File 79 of 114: the parts `rows22000E_780` … `rows22000E_789` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 267 s of the kernel: row 150 columns 47–57, row 150 columns 58–87,
row 150 columns 88–95, row 150 columns 96–102, row 150 columns 103–108, row 150 columns 109–114, row 150 columns
115–271, row 151 columns 0–46, row 151 columns 47–58, row 151 columns 59–87), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_780 : rowsJD 150 151 47 58 ≤ 15550139580030 := by decide +kernel

theorem rows22000E_781 : rowsJD 150 151 58 88 ≤ 272819797430216 := by decide +kernel

theorem rows22000E_782 : rowsJD 150 151 88 96 ≤ 476365550323225 := by decide +kernel

theorem rows22000E_783 : rowsJD 150 151 96 103 ≤ 479046388438937 := by decide +kernel

theorem rows22000E_784 : rowsJD 150 151 103 109 ≤ 415785951763297 := by decide +kernel

theorem rows22000E_785 : rowsJD 150 151 109 115 ≤ 405598753026217 := by decide +kernel

theorem rows22000E_786 : rowsJD 150 151 115 272 ≤ 1752704417439419 := by decide +kernel

theorem rows22000E_787 : rowsJD 151 152 0 47 ≤ 41741982643541 := by decide +kernel

theorem rows22000E_788 : rowsJD 151 152 47 59 ≤ 17878972325007 := by decide +kernel

theorem rows22000E_789 : rowsJD 151 152 59 88 ≤ 273132361628603 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_780
#print axioms SieveDeep.rows22000E_789
