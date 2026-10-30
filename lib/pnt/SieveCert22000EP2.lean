/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 10–19 of 1136

File 2 of 114: the parts `rows22000E_10` … `rows22000E_19` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 206 s of the kernel: rows 33–33, rows 34–34, rows 35–35, rows
36–36, row 37 columns 0–36, row 37 columns 37–271, row 38 columns 0–36, row 38 columns 37–271, row 39 columns 0–36,
row 39 columns 37–271), each a sum of the costs (`rowsJD`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

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

theorem rows22000E_10 : rowsJD 33 34 0 272 ≤ 328169115754507 := by decide +kernel

theorem rows22000E_11 : rowsJD 34 35 0 272 ≤ 350438390704946 := by decide +kernel

theorem rows22000E_12 : rowsJD 35 36 0 272 ≤ 371974771579462 := by decide +kernel

theorem rows22000E_13 : rowsJD 36 37 0 272 ≤ 392391806070620 := by decide +kernel

theorem rows22000E_14 : rowsJD 37 38 0 37 ≤ 383864366987191 := by decide +kernel

theorem rows22000E_15 : rowsJD 37 38 37 272 ≤ 28517999601898 := by decide +kernel

theorem rows22000E_16 : rowsJD 38 39 0 37 ≤ 375613209096478 := by decide +kernel

theorem rows22000E_17 : rowsJD 38 39 37 272 ≤ 56648969822684 := by decide +kernel

theorem rows22000E_18 : rowsJD 39 40 0 37 ≤ 367767037893129 := by decide +kernel

theorem rows22000E_19 : rowsJD 39 40 37 272 ≤ 85826045028355 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_10
#print axioms SieveDeep.rows22000E_19
