/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 630–639 of 1136

File 64 of 114: the parts `rows22000E_630` … `rows22000E_639` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 284 s of the kernel: row 129 columns 0–46, row 129 columns 47–61,
row 129 columns 62–72, row 129 columns 73–79, row 129 columns 80–103, row 129 columns 104–111, row 129 columns
112–271, row 130 columns 0–46, row 130 columns 47–61, row 130 columns 62–72), each a sum of the costs (`rowsJD`) at
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

theorem rows22000E_630 : rowsJD 129 130 0 47 ≤ 125225461149807 := by decide +kernel

theorem rows22000E_631 : rowsJD 129 130 47 62 ≤ 82801835040814 := by decide +kernel

theorem rows22000E_632 : rowsJD 129 130 62 73 ≤ 83522647346289 := by decide +kernel

theorem rows22000E_633 : rowsJD 129 130 73 80 ≤ 259354500794798 := by decide +kernel

theorem rows22000E_634 : rowsJD 129 130 80 104 ≤ 288654285417890 := by decide +kernel

theorem rows22000E_635 : rowsJD 129 130 104 112 ≤ 303679727097980 := by decide +kernel

theorem rows22000E_636 : rowsJD 129 130 112 272 ≤ 1775037968746426 := by decide +kernel

theorem rows22000E_637 : rowsJD 130 131 0 47 ≤ 118857896354295 := by decide +kernel

theorem rows22000E_638 : rowsJD 130 131 47 62 ≤ 79596334020378 := by decide +kernel

theorem rows22000E_639 : rowsJD 130 131 62 73 ≤ 87238153446091 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_630
#print axioms SieveDeep.rows22000E_639
