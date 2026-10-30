/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 230–239 of 1136

File 24 of 114: the parts `rows22000E_230` … `rows22000E_239` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 265 s of the kernel: row 83 columns 37–47, row 83 columns 48–54,
row 83 columns 55–62, row 83 columns 63–70, row 83 columns 71–76, row 83 columns 77–81, row 83 columns 82–271, row
84 columns 0–37, row 84 columns 38–48, row 84 columns 49–55), each a sum of the costs (`rowsJD`) at most its bound,
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

theorem rows22000E_230 : rowsJD 83 84 37 48 ≤ 122813837365881 := by decide +kernel

theorem rows22000E_231 : rowsJD 83 84 48 55 ≤ 90548051277920 := by decide +kernel

theorem rows22000E_232 : rowsJD 83 84 55 63 ≤ 100005452855597 := by decide +kernel

theorem rows22000E_233 : rowsJD 83 84 63 71 ≤ 92812135760838 := by decide +kernel

theorem rows22000E_234 : rowsJD 83 84 71 77 ≤ 69596481953042 := by decide +kernel

theorem rows22000E_235 : rowsJD 83 84 77 82 ≤ 82100130634672 := by decide +kernel

theorem rows22000E_236 : rowsJD 83 84 82 272 ≤ 44354483149930 := by decide +kernel

theorem rows22000E_237 : rowsJD 84 85 0 38 ≤ 212687484126577 := by decide +kernel

theorem rows22000E_238 : rowsJD 84 85 38 49 ≤ 120713597328643 := by decide +kernel

theorem rows22000E_239 : rowsJD 84 85 49 56 ≤ 93660799629764 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_230
#print axioms SieveDeep.rows22000E_239
