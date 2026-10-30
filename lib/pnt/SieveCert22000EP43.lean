/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 420–429 of 1136

File 43 of 114: the parts `rows22000E_420` … `rows22000E_429` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 262 s of the kernel: row 104 columns 39–52, row 104 columns 53–66,
row 104 columns 67–74, row 104 columns 75–82, row 104 columns 83–88, row 104 columns 89–92, row 104 columns 93–96,
row 104 columns 97–99, row 104 columns 100–102, row 104 columns 103–271), each a sum of the costs (`rowsJD`) at most
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

theorem rows22000E_420 : rowsJD 104 105 39 53 ≤ 176176948086807 := by decide +kernel

theorem rows22000E_421 : rowsJD 104 105 53 67 ≤ 111925399068253 := by decide +kernel

theorem rows22000E_422 : rowsJD 104 105 67 75 ≤ 56351630175413 := by decide +kernel

theorem rows22000E_423 : rowsJD 104 105 75 83 ≤ 25961567782830 := by decide +kernel

theorem rows22000E_424 : rowsJD 104 105 83 89 ≤ 44075787078615 := by decide +kernel

theorem rows22000E_425 : rowsJD 104 105 89 93 ≤ 61362867495894 := by decide +kernel

theorem rows22000E_426 : rowsJD 104 105 93 97 ≤ 116175658875497 := by decide +kernel

theorem rows22000E_427 : rowsJD 104 105 97 100 ≤ 126693942709995 := by decide +kernel

theorem rows22000E_428 : rowsJD 104 105 100 103 ≤ 161721708083790 := by decide +kernel

theorem rows22000E_429 : rowsJD 104 105 103 272 ≤ 130111203639402 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_420
#print axioms SieveDeep.rows22000E_429
