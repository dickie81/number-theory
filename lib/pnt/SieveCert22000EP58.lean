/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 570–579 of 1136

File 58 of 114: the parts `rows22000E_570` … `rows22000E_579` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 263 s of the kernel: row 121 columns 0–41, row 121 columns 42–61,
row 121 columns 62–71, row 121 columns 72–79, row 121 columns 80–85, row 121 columns 86–90, row 121 columns 91–114,
row 121 columns 115–271, row 122 columns 0–42, row 122 columns 43–61), each a sum of the costs (`rowsJD`) at most
its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_570 : rowsJD 121 122 0 42 ≤ 146695387042030 := by decide +kernel

theorem rows22000E_571 : rowsJD 121 122 42 62 ≤ 136645368148622 := by decide +kernel

theorem rows22000E_572 : rowsJD 121 122 62 72 ≤ 119584735312024 := by decide +kernel

theorem rows22000E_573 : rowsJD 121 122 72 80 ≤ 120393156766912 := by decide +kernel

theorem rows22000E_574 : rowsJD 121 122 80 86 ≤ 186687411722670 := by decide +kernel

theorem rows22000E_575 : rowsJD 121 122 86 91 ≤ 161116266929968 := by decide +kernel

theorem rows22000E_576 : rowsJD 121 122 91 115 ≤ 301613645468549 := by decide +kernel

theorem rows22000E_577 : rowsJD 121 122 115 272 ≤ 865940929176424 := by decide +kernel

theorem rows22000E_578 : rowsJD 122 123 0 43 ≤ 148517230215974 := by decide +kernel

theorem rows22000E_579 : rowsJD 122 123 43 62 ≤ 126222104784151 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_570
#print axioms SieveDeep.rows22000E_579
